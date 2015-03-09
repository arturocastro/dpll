//   Copyright (C) 2015 Dmitry Tsarkov and The University of Manchester.
//
//   This is free software: you can redistribute it and/or modify
//   it under the terms of the GNU General Public License as published by
//   the Free Software Foundation, either version 3 of the License, or
//   (at your option) any later version.
//   iProver is distributed in the hope that it will be useful,
//   but WITHOUT ANY WARRANTY; without even the implied warranty of
//   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
//   See the GNU General Public License for more details.
//   You should have received a copy of the GNU General Public License
//   along with iProver.  If not, see <http://www.gnu.org/licenses/>.

// --------------------------------------------------------------------------
// Additional code tagged in comments as "New Code"
// By Arturo Isai Castro Perpuli, 9555767
// University of Manchester, COMP60332 assignment
// Performed extensions: Activity Heuristics
// --------------------------------------------------------------------------

import java.io.*;
import java.util.*;

// minimal DPLL Sat Solver
public class DPLL {

	//
	// exceptions
	//
	public class Unsatisfiable extends Exception {
		private static final long serialVersionUID = 1L;
	}

	public class Satisfiable extends Exception {
		private static final long serialVersionUID = 1L;
	}

	public class Conflict extends Exception {
		private static final long serialVersionUID = -1324773608971346326L;
	}

	//
	// debug
	//
	static boolean DEBUG = false;

	static void dbg(String s) {
		if (DEBUG) {
			System.out.println(s);
		}
	}

	//
	// work with vars
	//

	// get variable out of lit
	static int lit2var(int lit) {
		return Math.abs(lit);
	}

	// get literal out of var and polarity
	static int getLit(boolean pos, int var) {
		return pos ? var : -var;
	}

	static boolean isPos(int lit) {
		return lit > 0;
	}

	//
	// clauses
	//

	private class Clause {

		// set of literals
		private List<Integer> lits;
		// set to true if clause is satisfied
		boolean sat;

		// init c'tor
		Clause(Collection<Integer> l) {
			lits = new ArrayList<Integer>(l);
			sat = false;
			dbg("DPLL.Clause.Clause(): " + lits);
		}

		// literals
		public List<Integer> getLits() {
			return lits;
		}

		// sat
		boolean isSat() {
			return sat;
		}

		void setSat(boolean s) {
			// dbg("DPLL.Clause.setSat(): " + lits + " " + s);
			sat = s;
		}

		// literal lit has known value now
		public void propagate(int lit) throws Conflict {

			// if the clause is satisfied -- nothing to do
			if (sat)
				return;

			// number of undefined literals
			int nUndef = 0;
			// literal for the unit clause (if any)
			int unit = 0;

			// check whether clause become unit/empty
			for (int l : lits) {
				int var = lit2var(l);
				if (varInit[var]) {
					// var is inited
					if (varValue[var] == isPos(l)) {
						// make the whole clause sat
						setSat(true);
						return;
					} else {
						// ineffective literal; do nothing
					}
				} else {
					// not inited yet: remember it
					unit = l;
					nUndef++;
				}
			}

			// check whether there are unchecked values
			if (nUndef == 0) {
				// clause is unsat
				throw new Conflict();
			}
			if (nUndef == 1) {
				// here clause became a unit one
				sat = true;
				dbg("DPLL.Clause.propagate(): " + lits + " unit " + unit);
				addUnitProp(unit);
			}
		}
	}

	// register new clause
	private void registerClause(List<Integer> lits) throws Unsatisfiable, Conflict {
		Set<Integer> args = new HashSet<Integer>();
		for (int lit : lits) {
			if (args.contains(-lit)) {
				// always sat -- nothing to do
				dbg("DPLL.registerClause(): sat " + lits);
				return;
			}
			args.add(lit);
		}
		if (args.isEmpty()) {
			// empty clause -- unsat
			throw new Unsatisfiable();
		}
		if (args.size() == 1) {
			// unit clause -- don't need to register it
			dbg("DPLL.registerClause(): unit " + lits);
			addUnitProp(args.iterator().next());
		} else {
			// normal clause: create and register
			Clause cl = new Clause(args);
			clauses.add(cl);
			for (int l : args) {
				lit2clauses.get(l).add(cl);
			}
		}
	}

	public static void main(String[] args) throws IOException {
		DPLL dpll = new DPLL();
		InputStream is = System.in;
		if (args.length > 0)
			is = new FileInputStream(args[0]);
		try {
			dpll.readInput(is);
			dpll.solve();
		} catch (Satisfiable sat) {
			// DO NOT CHANGE!! used in comparison
			System.out.println("sat");
			dpll.printModel();
		} catch (Unsatisfiable unsat) {
			// DO NOT CHANGE!! used in comparison
			System.out.println("unsat");
		}
	}

	//
	// solver state
	//

	// number of vars
	int nVars;
	// number of decisions
	int nDecisions = 0;

	// all clauses
	List<Clause> clauses = new ArrayList<Clause>();
	// map from literals to the clauses that use them
	Map<Integer, List<Clause>> lit2clauses;

	// var initialised?
	boolean varInit[];
	// var value; irrelevant for non-init vars
	boolean varValue[];
	// is var decision or implied
	boolean varDecision[];

	// unit propagation queue
	private Queue<Integer> upQueue = new LinkedList<Integer>();

	// undefined vars queue -- replaced by order
	Queue<Integer> varQueue = new LinkedList<Integer>();
        

	// trail -- all the literal assignments in chronological order
	Deque<Integer> trail = new ArrayDeque<Integer>();

	//
	// methods
	//

	// init all structures wrt the number of vars
	void init(int n) {
		dbg("DPLL.init(): nVars = " + n);
		nVars = n;

		varInit = new boolean[nVars + 1];
		varValue = new boolean[nVars + 1];
		varDecision = new boolean[nVars + 1];
		lit2clauses = new HashMap<Integer, List<Clause>>();

		// New code
		order = new VarOrder(n);

		// set the defaults
		for (int i = 1; i <= n; i++) {
			varInit[i] = false;
			varValue[i] = false;
			varDecision[i] = false;
			varQueue.add(i);
			
			order.newVar(i);
			
			lit2clauses.put(i, new ArrayList<Clause>());
			lit2clauses.put(-i, new ArrayList<Clause>());
		}
	}

	public void printModel() {
		for (int i = 1; i <= nVars; i++) {
			if (i > 1)
				System.out.print(",");
			System.out.print("x" + i + "=");
			if (varInit[i])
				System.out.print(varValue[i] ? 1 : 0);
			else
				System.out.print("?");
		}
		System.out.println();
	}

	//
	// unit propagation
	//

	// add literal to a unit propagation queue
	void addUnitProp(int lit) throws Conflict {
		// check if given unit is already scheduled for propagation
		if (upQueue.contains(lit)) {
			return;
		}
		int var = lit2var(lit);
		// dbg("DPLL.addUnitProp(): " + lit);
		if ((varInit[var] && varValue[var] != isPos(lit)) || upQueue.contains(-lit)) {
			// either model or unit queue contain contrary literal
			dbg("DPLL.addUnitProp(): conflict " + lit);
			throw new Conflict();
		}
		upQueue.add(lit);
	}

	// propagate unit clauses
	private void propagate() throws Conflict {
		while (!upQueue.isEmpty()) {
			// get the first literal to propagate
			int lit = upQueue.element();
			upQueue.remove();
			unitPropagate(lit);
		}
	}

	// perform unit propagation
	private void unitPropagate(int lit) throws Conflict {
		dbg("DPLL.unitPropagate(): " + lit);
		// check conflict
		int var = lit2var(lit);
		if (varInit[var]) // already initialised
		{
			if (getLit(varValue[var], var) == -lit) {
				// conflict here
				throw new Conflict();
			}

		} else {
			// need to initialise variable
			varInit[var] = true;
			varValue[var] = (lit > 0);
			varDecision[var] = false;
			varQueue.remove(var);
		}
		// record that literal gets value
		trail.push(lit);
		// mark all clauses with lit as satisfied
		for (Clause cl : lit2clauses.get(lit)) {
			if (!cl.isSat()) {
				cl.setSat(true);
			}
		}
		// propagate new information into all affected clauses
		for (Clause cl : lit2clauses.get(-lit)) {
			cl.propagate(lit);
		}
	}

	//
	// decide new literal
	//
	private void decide() throws Satisfiable, Conflict {
		// get the first element in the queue
		// that is uninitialised
		int var = getDecideVar();
		dbg("After decide");
		varInit[var] = true;
		// assign it to true
		varValue[var] = true;
		// mark as decided
		varDecision[var] = true;
		// report
		++nDecisions;
		dbg("DPLL.decide(): " + var + " d:" + nDecisions);
		// add variable to the propagation queue
		addUnitProp(var);
	}

	// get unassigned var
	int getDecideVar() throws Satisfiable {
		while (!varQueue.isEmpty()) {
		        // New code

		        // Get variable with highest activity instead of just the first of varQueue
		        int var = order.select();
			//int var = varQueue.element();
			
			if (var == -1) {
			    var = varQueue.element();
			}

			// Remove actual max var found instead of first of varQueue
			varQueue.remove(var);
			if (!varInit[var]) {
				// uninitialised var
				return var;
			}
		}
		// no vars to decide -- the problem is SAT
		throw new Satisfiable();
	}

	//
	// main method that solves the problem
	//
	private void solve() throws Satisfiable, Unsatisfiable {
		dbg("DPLL.solve(): Solving...");
		// exit via exceptions
		while (true) {
		    dbg("while...");
			try {
				// reset optimisation here
				//if ( needReset() )
				//        resetState();

				// propagate unit clauses
				dbg("before propagate");
				propagate();
				dbg("after propagate");

				// decide new literal
				decide();
			} catch (Conflict c) {
				// do backtrack etc
				analyseConflict(c);
				// clause learning here
				// addClause(c);
				// continue the loop

				// IF top-level conflict found THEN
				//     return UNSAT
				// ELSE
				//     backtrack()
			}
		}
	}

	private void analyseConflict(Conflict c) throws Unsatisfiable {
		// TODO Auto-generated method stub
		if (nDecisions == 0) {
			// no choices before -- problem unsat
			throw new Unsatisfiable();
		}
		// we reduce number of decisions
		nDecisions--;
		// we backtrack to the last decision point
		// at that point unit queue was empty
		upQueue.clear();
		// remove SAT flag from all clauses
		for (Clause cl : clauses) {
			cl.setSat(false);
		}
		// unassign all variables up to the latest decision one
		while (!trail.isEmpty()) {
			int lit = trail.pop();
			int var = lit2var(lit);
			dbg("DPLL.analyseConflict(): lit " + lit + ", var " + var);
			// vars in trail should be defined
			assert (varInit[var]);

			if (varDecision[var]) {

			        // New code
			        varBumpActivity(var);

				// decision var: flip the value
				boolean newPos = !varValue[var];
				varValue[var] = newPos;
				// remove the decision flag
				varDecision[var] = false;
				// add the new value to the UP queue
				int newlit = getLit(newPos, var);
				upQueue.add(newlit);
				dbg("DPLL.analyseConflict(): new lit " + newlit);
				// exit the loop
				break;
			} else {
				// regular var: just remove valuation
				varInit[var] = false;
				// add it to the var queue
				varQueue.add(var);
				order.newVar(var);
			}
		}
	}

	private void readInput(InputStream is) throws IOException, Unsatisfiable {
		BufferedReader in = new BufferedReader(new InputStreamReader(is));
		String s;
		while ((s = in.readLine()) != null && s.length() != 0) {
			if (s.startsWith("p")) {
				// prefix: fills number of vars
				int n = Integer.parseInt(s.split(" ")[2]);
				init(n);
				continue;
			} else if (s.startsWith("c")) {
				// comment: just skip
				continue;
			}
			// just a regular clause
			List<Integer> lits = new ArrayList<Integer>();
			for (String ss : s.split(" ")) {
				int l = Integer.parseInt(ss);
				if (l != 0)
					lits.add(l);
			}
			try {
				System.out.println("input clause: [" + s + "]");
				registerClause(lits);
			} catch (Conflict e) {
				// conflict in the input: input is unsat
				throw new Unsatisfiable();
			}
		}
	}

    // NEW CODE!

    // Constants
    
    final double kVarDecay = 2.0;
    final double kDoubleLimit = 1.0e100;
    final double kScaleFactor = 1.0e-100;

    // Variables

    double varIncrement = 1.0;
    
    VarOrder order;

    // Routines for activity heuristics, as seen in Minisat Paper - Figure 14.
    void varBumpActivity(int var) {
	final double act = order.incrActivity(var, varIncrement);

	if (act == -1) {
	    return;
	}

	if (act >= kDoubleLimit) {
	    varRescaleActivity();
	}

	order.update();
    }

    void varDecayActivity() {
	varIncrement *= kVarDecay; 
    }

    void varRescaleActivity() {
	order.rescaleActivities(kScaleFactor);
	varIncrement *= kScaleFactor;
    }

    // Implementation of VarOrder interface in MiniSat paper - Figure 4
    private class VarOrder {
	
	// Comparable pair of variable index and corresponding activity.
	private class SimpleHash implements Comparable<SimpleHash> {
	    int varIx;
	    double activity;
	    
	    SimpleHash(int pvarIx, double pactivity) {
		varIx = pvarIx;
		activity = pactivity;
	    }

	    @Override
	    public int compareTo(SimpleHash o) {
		if (activity == o.activity) {
		    return 0;
		}
		else {
		    return activity < o.activity ? 1 : -1;
		}
	    }
	}

	// Data structure to get var with max activity.
	PriorityQueue<SimpleHash> _pq;
	// Buffer to store activities when they are dequeue'd from _pq
	double acts[];

	public VarOrder(int n) {
	    _pq = new PriorityQueue<SimpleHash>(n + 1);
	    acts = new double[n + 1];
	}

	public void newVar(int ix) {
	    // Restore previous activity value (init to zero).
	    _pq.add(new SimpleHash(ix, acts[ix]));
	}

	// Heapify.
	public void update() {
	    // It's ugly, but it does the job.
	    _pq.add(_pq.poll());
	}

	// Get element with highest activity.
	public int select() {
	    SimpleHash head = _pq.poll();

	    if (head == null) {
		return -1;
	    } else {
		updateActs(head);

		return head.varIx;
	    }
	}

	// Search for variable's activity, increment it and return the new value.
	public double incrActivity(int var, double incr) {
	    for (SimpleHash pair : _pq) {
		if (pair.varIx == var) {
		    pair.activity += incr;

		    updateActs(pair);

		    return pair.activity;
		}
	    }

	    // var not found on _pq.
	    return -1.0;
	}

	// Rescale all activities down.
	public void rescaleActivities(double scaleFactor) {
	    for (SimpleHash pair : _pq) {
		pair.activity *= scaleFactor;
		
		updateActs(pair);
	    }
	}

	void updateActs(SimpleHash pair) {
	    acts[pair.varIx] = pair.activity;
	}
    }

    // UNUSED
    private boolean needReset() {
	return true;
    }

    private void resetState() {
	
    }	
}
