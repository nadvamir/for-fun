/**
 * A constraint programming solution to the New Scientist's
 * Enigma Number 1768 (Die hard).
 * http://www.newscientist.com/article/mg21929360.600-enigma-number-1768.html
 *
 * Lot's of magic numbers, but this was never expected to be general...
 * (c) Maksim Solovjov, 2014
 */
import java.util.*;
import java.io.*;
import static choco.Choco.*;
import choco.cp.model.CPModel;
import choco.cp.solver.CPSolver;
import choco.kernel.model.Model;
import choco.kernel.model.*;
import choco.kernel.model.constraints.*;
import choco.kernel.solver.Solver;
import choco.kernel.model.variables.integer.*;

public class Enigma {
    Model model, model2;  
    Solver solver, solver2; 
    // die stores the face values of the big die.
    // numeration of sides goes from 0,
    // and follows right handed die
    IntegerVariable[] die;
    // dice stores 4 face values of every side of a big die,
    // which should add up to the numbers we calculated
    // in the first part. 
    // 0 -- top-left
    // 1 -- top-right
    // 2 -- bottom-left
    // 3 -- bottom-right
    // If you hold a regular die with 1 on top, and 2 towards you,
    // then for 2, 3, 4 and 5 top is where you'd expect it to be,
    // and for 1 and 6 top is away from you.
    IntegerVariable[][] dice;
    
    // die sides can take any of primes or perfect squares values
    int allValues[] = {4, 5, 7, 9, 11, 13, 16, 17, 19, 23};

    // all values apart from 4 are possible
    int visibleVals[] = {1, 2, 3, 5, 6};
    // values that can be taken at corners
    int allowedCorners[][] = {
        {1, 2, 3},
        {2, 6, 3},
        {5, 1, 3},
        {6, 5, 3},
    };
    // description of corners bordering side 3
    // first number -- side, second number -- corner
    int side3Corners[][][] = {
        {{2, 0}, {0, 3}, {1, 1}},
        {{2, 1}, {4, 0}, {0, 1}},
        {{2, 2}, {1, 3}, {5, 2}},
        {{2, 3}, {5, 0}, {4, 2}},
    };
    // description of corners bordering side 4
    // first number -- side, second number -- corner
    int side4Corners[][][] = {
        {{3, 0}, {0, 0}, {4, 1}},
        {{3, 1}, {1, 0}, {0, 2}},
        {{3, 2}, {4, 3}, {5, 1}},
        {{3, 3}, {5, 3}, {1, 2}},
    };

    //---------------------------------------------------------------------------
    // control flow
    //---------------------------------------------------------------------------
    public Enigma() {
        buildModelForSideVals();
    }

    // gives a first solution that satisfies both problems
    void solve() {
        if (!solver.solve()) {
            System.out.println("no solutions");
        } else {
            do {
                buildModelForAssemblingDie();
            } while (!solver2.solve() && solver.nextSolution());
            printResult();
            stats(); // will probably crash if there is no solution after all
        }
    }

    //---------------------------------------------------------------------------
    // model for the first part of a problem
    //---------------------------------------------------------------------------
    // build a model to find the values for every side of a big die
    void buildModelForSideVals() {
        model  = new CPModel();
        solver = new CPSolver();

        // create the variables
        die = makeIntVarArray("side", 6, allValues);

        // so it happens that every perfect square has to occur there exactly once
        model.addConstraint(occurrence(1, die, 4));
        model.addConstraint(occurrence(1, die, 9));
        model.addConstraint(occurrence(1, die, 16));

        // opposite sides are equal
        IntegerExpressionVariable s1 = sum(die[0], die[5]);
        IntegerExpressionVariable s2 = sum(die[1], die[4]);
        IntegerExpressionVariable s3 = sum(die[2], die[3]);
        model.addConstraint(and(eq(s1, s2), eq(s2, s3)));

        // every variable is different in our die
        model.addConstraint(allDifferent(die));

        // upload model to solver
        solver.read(model);
    }

    //---------------------------------------------------------------------------
    // model for the second part of a problem
    //---------------------------------------------------------------------------
    // build a model to assemble the big die from little dies,
    // already knowing the values of the sides
    void buildModelForAssemblingDie() {
        model2  = new CPModel();
        solver2 = new CPSolver();

        // create variables for the little dice
        dice = new IntegerVariable[6][4];
        for (int i = 0; i < 6; ++i) {
            for (int j = 0; j < 4; ++j) {
                dice[i][j] = new IntegerVariable("Small die", visibleVals);
            }
        }

        // sum of the sides should satisfy the problem
        for (int i = 0; i < 6; ++i) {
            model2.addConstraint(eq(solver.getVar(die[i]).getVal(), sum(dice[i])));
        }

        // I only need to constrain two sides
        constrainSide(2);
        constrainSide(3);

        // upload model to solver
        solver2.read(model2);
    }

    // add constraints for every corner of this side
    void constrainSide(int s) {
        IntegerVariable[][] corners = getCorners(s);
        for (int i = 0; i < 4; ++i) {
            constrainCorner(corners[i]);
        }
    }

    // constrain corner to only have allowed combinations
    void constrainCorner(IntegerVariable[] vals) {
        Constraint cs[] = new Constraint[allowedCorners.length * 3];
        for (int i = 0; i < allowedCorners.length; ++i) {
            cs[i*3]   = and(eq(vals[0], allowedCorners[i][0]),
                            eq(vals[1], allowedCorners[i][1]),
                            eq(vals[2], allowedCorners[i][2]));
            cs[i*3+1] = and(eq(vals[0], allowedCorners[i][1]),
                            eq(vals[1], allowedCorners[i][2]),
                            eq(vals[2], allowedCorners[i][0]));
            cs[i*3+2] = and(eq(vals[0], allowedCorners[i][2]),
                            eq(vals[1], allowedCorners[i][0]),
                            eq(vals[2], allowedCorners[i][1]));
        }

        // possibly not the most ellegant way to do it...
        // since it depends on there being 4 allowed corners...
        model2.addConstraint(or(
            cs[0], cs[1], cs[2], cs[3], cs[4], cs[5],
            cs[6], cs[7], cs[8], cs[9], cs[10], cs[11]));
    }

    // return all corners for the given side
    IntegerVariable[][] getCorners(int s) {
        // choose which corners we are returning
        int side[][][] = side3Corners;
        if (3 == s) { // 0-indexed
            side = side4Corners;
        }

        IntegerVariable[][] corners = new IntegerVariable[4][3];
        // there are four corners on every side
        for (int i = 0; i < 4; ++i) {
            // there are three adjacent sides of a small die for every corner
            for (int j = 0; j < 3; ++j) {
                corners[i][j] = dice[side[i][j][0]][side[i][j][1]];
            }
        }
        return corners;
    }

    //---------------------------------------------------------------------------
    // printing out the result
    //---------------------------------------------------------------------------
    // prints out the answers to first and second parts of the problem
    void printResult() {
        System.out.println("First bit:");
        for (int i = 0; i < 6; ++i) {
            System.out.print(solver.getVar(die[i]).getVal() + " ");
        }
        System.out.println();

        System.out.println("Second bit:");
        int ones = 0, twos = 0;
        for (int i = 0; i < 6; ++i) {
            for (int j = 0; j < 4; ++j) {
                if (1 == solver2.getVar(dice[i][j]).getVal()) {
                    ones += 1;
                } else if (2 == solver2.getVar(dice[i][j]).getVal()) {
                    twos += 1;
                }
            }
        }
        System.out.println("Ones: " + ones + ", twos: " + twos);

        for (int i = 0; i < 6; ++i) {
            for (int j = 0; j < 4; ++j) {
                System.out.print(solver2.getVar(dice[i][j]).getVal() + " ");
            }
            System.out.println();
        }
    }

    // runtime statistics of the last successful try
    // kinda useless, should probably accumulate them :/
    void stats() {
        System.out.println("Part 1: nodes: "+ solver.getNodeCount() +"   cpu: "+ solver.getTimeCount());
        System.out.println("Part 2: nodes: "+ solver2.getNodeCount() +"   cpu: "+ solver2.getTimeCount());
    }
    
    //---------------------------------------------------------------------------
    // main block
    //---------------------------------------------------------------------------
    public static void main(String[] args)  throws IOException {
        Enigma e = new Enigma();
        e.solve();
    }
}

