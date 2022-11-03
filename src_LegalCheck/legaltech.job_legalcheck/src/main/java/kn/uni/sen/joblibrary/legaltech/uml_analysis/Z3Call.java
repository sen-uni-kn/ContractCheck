package kn.uni.sen.joblibrary.legaltech.uml_analysis;

import java.util.HashMap;
import java.util.LinkedList;

import com.microsoft.z3.AST;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Model;
import com.microsoft.z3.Optimize;
import com.microsoft.z3.Quantifier;
import com.microsoft.z3.RealExpr;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Statistics;
import com.microsoft.z3.Status;

import kn.uni.sen.jobscheduler.common.resource.ResourceString;

/**
 * interface to run the Z3 SMT solver
 *  
 * @author Martin Koelbl
 */
public class Z3Call
{
	// Model modelSolution;
	String eliminatedModel = null;

	double memoryS = Double.NaN;
	double memory = Double.NaN;
	int varCount = 0;
	int assertCount = 0;
	double timeDif = 0;
	public static int timeout = 0;
	Model model = null;
	Expr<?>[] objs = null;
	boolean sat = false;
	BoolExpr[] unsatCore = null;

	public Z3Call()
	{
		com.microsoft.z3.Native.resetMemory();
		com.microsoft.z3.Native.finalizeMemory();
		System.gc();
	}

	protected void finalize()
	{
		ctx.close();
	}

	Context ctx = null;

	private Context createContext(boolean unsat)
	{
		HashMap<String, String> cfg = new HashMap<String, String>();
		cfg.put("model", "true");
		if (unsat)
			cfg.put("unsat-core", "true");
		if (timeout >= 0)
		{
			cfg.put("timeout", "" + timeout);
		}
		close();
		Context ctx = new Context(cfg);
		this.ctx = ctx;
		return ctx;
	}

	public void close()
	{
		if (ctx != null)
			ctx.close();
		ctx = null;
	}

	public boolean example()
	{
		System.out.println("XOR - test start");
		Context ctx = createContext(false);
		BoolExpr x = ctx.mkBoolConst("x");
		BoolExpr y = ctx.mkBoolConst("y");
		BoolExpr x_xor_y = ctx.mkXor(x, y);

		Model m = check(ctx, x_xor_y, Status.SATISFIABLE);
		System.out.println(m);

		System.out.println("Interpretation of x: " + m.getConstInterp(x));
		System.out.println("Interpretation of y: " + m.getConstInterp(y));

		System.out.println("XOR - test end");
		return true;
	}

	static int count = 0;

	public boolean runFile(String modelFile, boolean unsat)
	{
		System.gc();
		sat = false;
		try
		{
			Context ctx = createContext(unsat);
			// String val = Version.getString();
			BoolExpr[] a = ctx.parseSMTLIB2File(modelFile, null, null, null, null);

			Optimize solver = ctx.mkOptimize();
			checkStatistic(solver.getStatistics(), true);
			if (unsat)
			{
				if (solver.Check(a) != Status.SATISFIABLE)
				{
					unsatCore = solver.getUnsatCore();
					checkStatistic(solver.getStatistics(), false);
					objs = null;
					return false;
				}
				solver = ctx.mkOptimize();
			}

			solver.fromFile(modelFile);
			if (solver.Check(a) != Status.SATISFIABLE)
			{
				checkStatistic(solver.getStatistics(), false);
				if (unsat)
					System.out.println("Error: Unsat with second run.");
				return false;
			}
			checkStatistic(solver.getStatistics(), false);

			Model m = solver.getModel(); // check(ctx, a, Status.SATISFIABLE);
			if (m != null)
			{
				model = m;
				sat = true;
			}

			// long t_diff = ((new Date()).getTime() - before.getTime()) / 1000;

			// System.out.println("SMT2 file read time: " + t_diff + " sec");
		} catch (Exception ex)
		{
			System.out.println(ex.toString());
			return false;
		}

		// long t_diff = ((new Date()).getTime() - before.getTime()) / 1000;
		// System.out.println("SMT2 file test took " + t_diff + " sec");
		return true;
	}

	BoolExpr[] getUnsatCore()
	{
		return unsatCore;
	}

	Expr<?>[] getObjectives()
	{
		return objs;
	}

	public Model checkSat(String modelFile)
	{
		System.gc();
		try
		{
			Context ctx = createContext(false);
			BoolExpr[] a = ctx.parseSMTLIB2File(modelFile, null, null, null, null);
			Optimize solver = ctx.mkOptimize();
			if (solver.Check(a) != Status.SATISFIABLE)
				return null;
			return solver.getModel();
		} catch (Exception ex)
		{
			System.out.println(ex.toString());
		}
		return null;
	}

	public Expr<?>[] checkSatObjectives(String modelFile)
	{
		System.gc();
		try
		{
			Context ctx = createContext(false);
			BoolExpr[] a = ctx.parseSMTLIB2File(modelFile, null, null, null, null);
			Optimize solver = ctx.mkOptimize();
			// Optimize.Handle mx = solver.MkMaximize(null);
			// mx.getLower();
			if (solver.Check(a) != Status.SATISFIABLE)
				return null;
			return solver.getObjectives();
		} catch (Exception ex)
		{
			System.out.println(ex.toString());
		}
		return null;
	}

	public void checkMetaData(String z3Code)
	{
		int count = ResourceString.countOccurrences(z3Code, "assert");
		if (count > assertCount)
			assertCount = count;
		count = ResourceString.countOccurrences(z3Code, "Real"); // declare-const
		if (count > varCount)
			varCount = count;
	}

	public void checkStatistic(Statistics statistics, boolean start)
	{
		if (statistics == null)
			return;
		com.microsoft.z3.Statistics.Entry mem = statistics.get("memory");
		com.microsoft.z3.Statistics.Entry time2 = statistics.get("time");
		if (start)
			memoryS = mem.getDoubleValue();
		else
		{
			if (mem != null)
				memory = mem.getDoubleValue();
			if (time2 != null)
				timeDif = time2.getDoubleValue();
			else
				timeDif = 0;
		}
	}

	// function is not used
	void visit(Expr<?> e)
	{
		if (e.isFuncDecl())
		{
			FuncDecl<?> f = e.getFuncDecl();
			System.out.println("application of " + f.getName() + ": " + e + "\n");
		} else if (e.isApp())
		{
			int num = e.getNumArgs();
			for (int i = 0; i < num; i++)
			{
				visit(e.getArgs()[i]);
			}
			// do something
			// Example: print the visited expression
			FuncDecl<?> f = e.getFuncDecl();
			System.out.println("application of " + f.getName() + ": " + e + "\n");
		} else if (e.isQuantifier())
		{
			visit(((Quantifier) e).getBody());
			// do something
		} else
		{
			System.out.println("error");
		}
	}

	int getCount(BoolExpr a)
	{
		// Iterate over the formula.
		LinkedList<Expr<?>> q = new LinkedList<Expr<?>>();
		q.add(a);

		int cnt = 0;
		while (q.size() > 0)
		{
			AST cur = (AST) q.removeFirst();
			cnt++;

			if (cur.getClass() == BoolExpr.class)
			{
				if (!(cur.isVar()))
					for (Expr<?> c : ((Expr<?>) cur).getArgs())
						q.add(c);
			} else if (cur.getClass() == Expr.class)
			{
				if (!(cur.isVar()))
					for (Expr<?> c : ((Expr<?>) cur).getArgs())
						q.add(c);
			} else if (cur.getClass() == RealExpr.class)
			{
				if (!(cur.isVar()))
					for (Expr<?> c : ((Expr<?>) cur).getArgs())
						q.add(c);

			} else if (cur.getClass() == Quantifier.class)
			{
			}
		}
		// System.out.println(cnt + " ASTs");
		return cnt;
	}

	Model check(Context ctx, BoolExpr f, Status sat)
	{
		Solver s = ctx.mkSolver();
		if (s.check(f) != sat)
			return null;
		if (sat == Status.SATISFIABLE)
			return s.getModel();
		return null;
	}

	public String getEliminatedModel()
	{
		return eliminatedModel;
	}

	public double getMemory()
	{
		return memory;
	}

	public int getVarCount()
	{
		return varCount;
	}

	public int getAssertCount()
	{
		return assertCount;
	}

	public double getTime()
	{
		return timeDif;
	}

	public Model getModel()
	{
		return model;
	}

	public boolean isSat()
	{
		return sat;
	}
}
