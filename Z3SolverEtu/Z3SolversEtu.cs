using System;
using System.Collections.Generic;
using System.Linq;
using Microsoft.Z3;
using Sudoku.Shared;

namespace Z3SolverEtu
{
    public class Z3CleanSolverEtu : Z3SolverBase
    {
        public override Sudoku.Shared.SudokuGrid Solve(Sudoku.Shared.SudokuGrid s)
        {
            return SolveEtuVersion(s);
        }

    }
    public abstract class Z3SolverBase : ISudokuSolver
    {
        public abstract SudokuGrid Solve(Sudoku.Shared.SudokuGrid s);

        protected static Context z3Context = new Context();

        // 9x9 matrix of integer variables
        static IntExpr[][] X = new IntExpr[9][];
        static BoolExpr _GenericContraints;

        private static Solver _reusableZ3Solver;

        static Z3SolverBase()
        {
            PrepareVariables();
        }

        public static BoolExpr GenericContraints
        {
            get
            {
                if (_GenericContraints == null)
                {
                    _GenericContraints = GetGenericConstraints();
                }
                return _GenericContraints;
            }
        }

        public static Solver ReusableZ3Solver
        {
            get
            {
                if (_reusableZ3Solver == null)
                {
                    _reusableZ3Solver = z3Context.MkSolver();
                    _reusableZ3Solver.Assert(GenericContraints);
                }
                return _reusableZ3Solver;
            }
        }


        BoolExpr GetPuzzleConstraint(Sudoku.Shared.SudokuGrid instance)
        {
            BoolExpr instance_c = z3Context.MkTrue();
            for (int i = 0; i < 9; i++)
                for (int j = 0; j < 9; j++)
                    if (instance.Cells[i][j] != 0)
                    {
                        instance_c = z3Context.MkAnd(instance_c,
                            (BoolExpr)
                            z3Context.MkEq(X[i][j], z3Context.MkInt(instance.Cells[i][j])));
                    }
            return instance_c;
        }

        static void PrepareVariables()
        {
            for (uint i = 0; i < 9; i++)
            {
                X[i] = new IntExpr[9];
                for (uint j = 0; j < 9; j++)
                    X[i][j] = (IntExpr)z3Context.MkConst(z3Context.MkSymbol("x_" + (i + 1) + "_" + (j + 1)), z3Context.IntSort);
            }
        }

        static BoolExpr GetGenericConstraints()
        {

            // each cell contains a value in {1, ..., 9}
            BoolExpr[][] cells_c = new BoolExpr[9][];
            for (uint i = 0; i < 9; i++)
            {
                cells_c[i] = new BoolExpr[9];
                for (uint j = 0; j < 9; j++)
                    cells_c[i][j] = z3Context.MkAnd(z3Context.MkLe(z3Context.MkInt(1), X[i][j]),
                        z3Context.MkLe(X[i][j], z3Context.MkInt(9)));
            }

            // each row contains a digit at most once
            BoolExpr[] rows_c = new BoolExpr[9];
            for (uint i = 0; i < 9; i++)
                rows_c[i] = z3Context.MkDistinct(X[i]);


            // each column contains a digit at most once
            BoolExpr[] cols_c = new BoolExpr[9];
            for (uint j = 0; j < 9; j++)
            {
                Expr[] column = new Expr[9];
                for (uint i = 0; i < 9; i++)
                    column[i] = X[i][j];

                cols_c[j] = z3Context.MkDistinct(column);
            }

            // each 3x3 square contains a digit at most once
            BoolExpr[][] sq_c = new BoolExpr[3][];
            for (uint i0 = 0; i0 < 3; i0++)
            {
                sq_c[i0] = new BoolExpr[3];
                for (uint j0 = 0; j0 < 3; j0++)
                {
                    Expr[] square = new Expr[9];
                    for (uint i = 0; i < 3; i++)
                        for (uint j = 0; j < 3; j++)
                            square[3 * i + j] = X[3 * i0 + i][3 * j0 + j];
                    sq_c[i0][j0] = z3Context.MkDistinct(square);
                }
            }

            var toReturn = z3Context.MkTrue();
            foreach (BoolExpr[] t in cells_c)
                toReturn = z3Context.MkAnd(z3Context.MkAnd(t), toReturn);
            toReturn = z3Context.MkAnd(z3Context.MkAnd(rows_c), toReturn);
            toReturn = z3Context.MkAnd(z3Context.MkAnd(cols_c), toReturn);
            foreach (BoolExpr[] t in sq_c)
                toReturn = z3Context.MkAnd(z3Context.MkAnd(t), toReturn);
            return toReturn;
        }

        protected virtual Solver GetSolver()
        {
            return z3Context.MkSolver();
        }

        protected virtual Solver GetReusableSolver()
        {
            return ReusableZ3Solver;
        }
        protected Sudoku.Shared.SudokuGrid SolveEtuVersion(Sudoku.Shared.SudokuGrid instance)
        {
            using (Context ctx = new Context())
            {
                Solver solver = ctx.MkSolver();
                IntExpr[,] cells = new IntExpr[9, 9];

                // Create integer variables for each cell
                for (int i = 0; i < 9; i++)
                {
                    for (int j = 0; j < 9; j++)
                    {
                        cells[i, j] = (IntExpr)ctx.MkConst(ctx.MkSymbol("cell_" + i.ToString() + "_" + j.ToString()), ctx.IntSort);
                    }
                }

                for (int i = 0; i < 9; i++)
                {
                    for (int j = 0; j < 9; j++)
                    {
                        if (instance.Cells[i][j] == 0)
                        {
                            // Add the constraint for each empty cell
                            solver.Assert(ctx.MkAnd(
                                // The value must be between 1 and 9
                                ctx.MkAnd(cells[i, j] >= ctx.MkInt(1), cells[i, j] <= ctx.MkInt(9)),
                                // The value must not already be present in the same row
                                ctx.MkNot(ctx.MkOr(Enumerable.Range(0, 9).Select(k => (BoolExpr)(ctx.MkEq(cells[i, j], cells[i, k]))))),
                                // The value must not already be present in the same column
                                ctx.MkNot(ctx.MkOr(Enumerable.Range(0, 9).Select(k => (BoolExpr)(ctx.MkEq(cells[i, j], cells[k, j]))))),
                                // The value must not already be present in the same 3x3 subgrid
                                ctx.MkNot(ctx.MkOr(Enumerable.Range(0, 3).SelectMany(x => Enumerable.Range(0, 3).Select(y => ctx.MkBool(cells[(i / 3) * 3 + x, (j / 3) * 3 + y] == cells[i, j])))))
                            ));
                        }
                        else
                        {
                            // Add the constraint for each filled cell
                            solver.Assert(ctx.MkEq(cells[i, j], ctx.MkInt(instance.Cells[i][j])));
                        }
                    }
                }

                if (solver.Check() == Status.SATISFIABLE)
                {
                    instance = instance.CloneSudoku();
                    Model model = solver.Model;
                    for (int i = 0; i < 9; i++)
                    {
                        for (int j = 0; j < 9; j++)
                        {
                            instance.Cells[i][j] = ((IntNum)model.Evaluate(cells[i, j])).Int;
                        }
                    }
                    return instance;
                }
                else
                {
                    Console.WriteLine("Failed to solve sudoku");
                    return instance;
                }
            }
        }

        protected Sudoku.Shared.SudokuGrid SolveOriginalVersion(Sudoku.Shared.SudokuGrid instance)
        {
            BoolExpr instance_c = z3Context.MkTrue();
            for (int i = 0; i < 9; i++)
                for (int j = 0; j < 9; j++)
                    instance_c = z3Context.MkAnd(instance_c,
                        (BoolExpr)
                        z3Context.MkITE(z3Context.MkEq(z3Context.MkInt(instance.Cells[i][j]), z3Context.MkInt(0)),
                            z3Context.MkTrue(),
                            z3Context.MkEq(X[i][j], z3Context.MkInt(instance.Cells[i][j]))));

            Solver s = z3Context.MkSolver();
            s.Assert(GenericContraints);
            s.Assert(instance_c);

            if (s.Check() == Status.SATISFIABLE)
            {
                instance = instance.CloneSudoku();
                Model m = s.Model;
                for (int i = 0; i < 9; i++)
                    for (int j = 0; j < 9; j++)
                    {
                        instance.Cells[i][j] = ((IntNum)m.Evaluate(X[i][j])).Int;
                    }
                return instance;


            }
            else
            {
                Console.WriteLine("Failed to solve sudoku");
                return instance;
            }
        }
    }
}