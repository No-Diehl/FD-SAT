#include "sat.h"
#include "../utils/timer.h"
#include <unistd.h> // for directory path
#include <cstdlib> // for exit-function
#include <fstream> // for file generation
#include <iostream>


using namespace std;

namespace sat {

/* Using two 2D vectors to store the state variables (facts) for the current and
   following time step.

vector<vector<int>> factsAtTnow;
vector<vector<int>> factsAtTplusOne;

 Using a 2D vector to store the operator variables for each time step.
   Each vector represents the time step at which an operator was executed
   (if true in the returned plan).

vector<vector<int>> operatorVars;*/

//void* solver = ipasir_init();

void sat_init(TaskProxy task_proxy,
    sat_capsule & capsule,
    vector<vector<int>> & factsAtTnow,
    vector<vector<int>> & factsAtTplusOne,
    vector<vector<int>> & operatorVars) {

    // Initially fill the corresponding vectors with the variables representing
    // the initial state and the following time step.
    for (size_t i=0; i<task_proxy.get_variables().size(); i++) {
        vector<int> mutexGroupNow;
        vector<int> mutexGroupPlusOne;
        for (int j=0; j<task_proxy.get_variables()[i].get_domain_size(); j++) {
            mutexGroupNow.push_back(capsule.new_variable());
            mutexGroupPlusOne.push_back(capsule.new_variable());
        }
        factsAtTnow.push_back(mutexGroupNow);
        factsAtTplusOne.push_back(mutexGroupPlusOne);
    }

    // Initially fill the vector with the variables representing which operator
    // was executed (if true in the returned plan) at t0.
    vector<int> operatorsAtTnow;
    for (size_t i=0; i<task_proxy.get_operators().size(); i++) {
        operatorsAtTnow.push_back(capsule.new_variable());
    }
    operatorVars.push_back(operatorsAtTnow);
}

/* Using two 3D vectors to store the state variables (facts) for the current and
   following time step.

vector<vector<vector<int>>> binaryFactsAtTnow;
vector<vector<vector<int>>> binaryFactsAtTplusOne;*/

void forbidden_binary_states(vector<vector<vector<int>>> & binaryFacts, void * solver) {
    for (size_t i=0; i<binaryFacts.size(); i++) {
        if (__builtin_popcount(binaryFacts[i].size()) != 1) {
            int bits = sizeof(int)*8-__builtin_clz(binaryFacts[i].size());
            int nxtPowOfTwo = 2;
            for (int i=1; i<bits; i++) {nxtPowOfTwo *= 2;}
            for (int j=binaryFacts[i].size(); j<nxtPowOfTwo; j++) {
                int count = 0;
                vector<int> forbiddenState;
                for (int k=binaryFacts[i][0].size()-1; k>=0; k--) {
                    if (j & (1 << k)) {
                        forbiddenState.push_back(binaryFacts[i][0][count]);
                        count++;
                    } else {
                        forbiddenState.push_back(-binaryFacts[i][0][count]);
                        count++;
                    }
                }
                assertOr(solver, forbiddenState);
            }
        }
    }
}

void sat_init_binary(TaskProxy task_proxy,
    sat_capsule & capsule,
    void * solver,
    vector<vector<vector<int>>> & binaryFactsAtTnow,
    vector<vector<vector<int>>> & binaryFactsAtTplusOne,
    vector<vector<int>> & operatorVars) {

    for (size_t i=0; i<task_proxy.get_variables().size(); i++) {
        vector<vector<int>> mutexGroupNow;
        vector<vector<int>> mutexGroupPlusOne;
        // Calculate number of needed variables to represent all facts of current mutex group.
        int binaryVars;
        /* 
        Differentiate between powers of 2 and other numbers. Group sizes of exact powers of 2
        need one bit less to represent all members.
        Note: __builtin_popcount(unsigned int x) returns the num of 1-bits in x
        */
        if (__builtin_popcount(task_proxy.get_variables()[i].get_domain_size()) == 1) {
            // Note: __builtin_ctz(unsigned int x) returns num of trailing 0-bits in x
            binaryVars = __builtin_ctz(task_proxy.get_variables()[i].get_domain_size());
        } else {
            // Note: __builtin_clz(unsigned int x) return the num of leading 0-bits in x
            binaryVars = sizeof(int)*8-__builtin_clz(task_proxy.get_variables()[i].get_domain_size());
        }
        // Vectors containing the template variables for a mutex group.
        vector<int> factBinaryVarsNow;
        vector<int> factBinaryVarsPlusOne;
        for (int j=0; j<binaryVars; j++) {
            factBinaryVarsNow.push_back(capsule.new_variable());
            factBinaryVarsPlusOne.push_back(capsule.new_variable());
        }
        // Push the binary fact encodings into a vector, a positive int representing a 1-bit
        // and a negative int representing a 0-bit using the registered template variables.
        for (int k=0; k<task_proxy.get_variables()[i].get_domain_size(); k++) {
            vector<int> factVarsStatesNow;
            vector<int> factVarsStatesPlusOne;
            for (int l=factBinaryVarsNow.size()-1; l>=0; l--) {
                if (k & (1 << l)) {
                    factVarsStatesNow.push_back(factBinaryVarsNow[factBinaryVarsNow.size()-1-l]);
                    factVarsStatesPlusOne.push_back(factBinaryVarsPlusOne[factBinaryVarsPlusOne.size()-1-l]);
                } else {
                    factVarsStatesNow.push_back(-factBinaryVarsNow[factBinaryVarsNow.size()-1-l]);
                    factVarsStatesPlusOne.push_back(-factBinaryVarsPlusOne[factBinaryVarsPlusOne.size()-1-l]);
                }
            }
            mutexGroupNow.push_back(factVarsStatesNow);
            mutexGroupPlusOne.push_back(factVarsStatesPlusOne);
        }
        binaryFactsAtTnow.push_back(mutexGroupNow);
        binaryFactsAtTplusOne.push_back(mutexGroupPlusOne);
    }
    //cout << "States at t0: " << binaryFactsAtTnow << endl;
    //cout << "States at t1: " << binaryFactsAtTplusOne << endl;

    // Find and add the unused binary states for the mutex groups.
    forbidden_binary_states(binaryFactsAtTnow, solver);
    forbidden_binary_states(binaryFactsAtTplusOne, solver);

    // Initially fill the vector with the variables representing which operator
    // was executed (if true in the returned plan) at t0.
    vector<int> operatorsAtTnow;
    for (size_t i=0; i<task_proxy.get_operators().size(); i++) {
        operatorsAtTnow.push_back(capsule.new_variable());
    }
    operatorVars.push_back(operatorsAtTnow);
    //cout << "Operators at t0: " << operatorVars << endl;
}

void sat_step(TaskProxy task_proxy,
    sat_capsule & capsule,
    vector<vector<int>> & factsAtTnow,
    vector<vector<int>> & factsAtTplusOne,
    vector<vector<int>> & operatorVars) {

    factsAtTnow.swap(factsAtTplusOne);
    // Replace all the variables in factsAtTplusOne with new variables for the current time step.
    for (size_t i=0; i<factsAtTplusOne.size(); i++) {
        for (size_t j=0; j<factsAtTplusOne[i].size(); j++) {
            factsAtTplusOne[i][j] = capsule.new_variable();
        }
    }

    // Create a new vector<int> with variables representing which operator was executed
    // (if true in the returned plan) at the current time step.
    vector<int> operatorsAtTnow;
    for (size_t i=0; i<task_proxy.get_operators().size(); i++) {
        operatorsAtTnow.push_back(capsule.new_variable());
    }
    operatorVars.push_back(operatorsAtTnow);
}

void sat_step_binary(TaskProxy task_proxy,
    sat_capsule & capsule,
    void * solver,
    vector<vector<vector<int>>> & binaryFactsAtTnow,
    vector<vector<vector<int>>> & binaryFactsAtTplusOne,
    vector<vector<int>> & operatorVars) {

    binaryFactsAtTnow.swap(binaryFactsAtTplusOne);
    // Replace all the variables in binaryFactsAtTplusOne with new variables for the current time step.
    for (size_t i=0; i<binaryFactsAtTplusOne.size(); i++) {
        vector<int> newVariables;
        if (newVariables.size()<=0) {
            for (size_t j=0; j<binaryFactsAtTplusOne[i][0].size(); j++) {
                newVariables.push_back(capsule.new_variable());
            }
        }
        for (size_t j=0; j<binaryFactsAtTplusOne[i].size(); j++) {;
            for (size_t k=0; k<binaryFactsAtTplusOne[i][j].size(); k++) {
                if (binaryFactsAtTplusOne[i][j][k] < 0) {
                    binaryFactsAtTplusOne[i][j][k] = -newVariables[k];
                } else {
                    binaryFactsAtTplusOne[i][j][k] = newVariables[k];
                }
                
            }
        }
    }
    //cout << "Variables for next timestep: " << binaryFactsAtTplusOne << endl;

    // Find and add forbidden states of the binary fact mutex groups.
    forbidden_binary_states(binaryFactsAtTplusOne, solver);

    // Create a new vector<int> with variables representing which operator was executed
    // (if true in the returned plan) at the current time step.
    vector<int> operatorsAtTnow;
    for (size_t i=0; i<task_proxy.get_operators().size(); i++) {
        operatorsAtTnow.push_back(capsule.new_variable());
    }
    operatorVars.push_back(operatorsAtTnow);
    //cout << "Operator vars for next timestep: " << operatorVars << endl;
}

void found_plan(int vars, TaskProxy task_proxy, void * solver, const vector<vector<int>> & operatorVars, bool binary) {
    PlanManager plan_man;
    if (binary) {
        plan_man.set_plan_filename("found_plan_binary");
    } else {
        plan_man.set_plan_filename("found_plan");
    }
    Plan plan;
    for (int v = 1; v <= vars; v++) {
        for (auto & it : operatorVars) {
            for (size_t i=0; i<it.size(); i++) {
                if (it[i] == v and ipasir_val(solver,v) > 0) {
                    plan.push_back(OperatorID(task_proxy.get_operators()[i].get_id()));
                }
            }
        }
    }
    plan_man.save_plan(plan, task_proxy);
}

bool sat_encoding(TaskProxy task_proxy, int steps) {
    // Start encoding timer here.
    utils::Timer enc_timer;

    /*
    Using two 2D vectors to store the state variables (facts) for the current and
    following time step.
    */
    vector<vector<int>> factsAtTnow;
    vector<vector<int>> factsAtTplusOne;

    /*
    Using a 2D vector to store the operator variables for each time step.
    Each vector represents the time step at which an operator was executed
    (if true in the returned plan).
    */
    vector<vector<int>> operatorVars;
    void * solver = ipasir_init();
    sat_capsule capsule;

    sat_init(task_proxy, capsule, factsAtTnow, factsAtTplusOne, operatorVars);

    // Add the variables reflecting the initial state of the problem.
    for (size_t i=0; i<factsAtTnow.size(); i++) {
        for (size_t j=0; j<factsAtTnow[i].size(); j++) {
            if ((size_t)task_proxy.get_initial_state().get_values()[i] == j) {
                assertYes(solver, factsAtTnow[i][j]);
            } else {
                assertNot(solver, factsAtTnow[i][j]);
            }
        }
    }
    int init_clauses = get_number_of_clauses();
    int mutex_clauses = 0;
    int operator_clauses = 0;
    int frame_axioms = 0;
    int operator_limit = 0;

    for (int timeStep=0; timeStep<steps; timeStep++) {
        // Testing forall encoding preparations.
        if (timeStep == 0) {
            sat_forall(task_proxy, capsule, factsAtTnow, operatorVars);
        }

        int curr_clauses;
        if (timeStep == 0) {
            curr_clauses = get_number_of_clauses();
        }
        // Add clauses reflecting the mutex condition of a group of variables.
        for (size_t i=0; i<factsAtTplusOne.size(); i++) {
            atLeastOne(solver, capsule, factsAtTplusOne[i]);
            atMostOne(solver, capsule, factsAtTplusOne[i]);
        }
        if (timeStep == 0) {
            mutex_clauses = get_number_of_clauses()-curr_clauses;
        }

        // Vector to collect actions/operators executing the same effects.
        vector<vector<vector<int>>> frameAxioms;
        for (size_t i=0; i<task_proxy.get_variables().size(); i++) {
            vector<vector<int>> variable;
            for (int j=0; j<task_proxy.get_variables()[i].get_domain_size(); j++) {
                vector<int> fact;
                variable.push_back(fact);
            }
        frameAxioms.push_back(variable);
        }

        if (timeStep == 0) {
            curr_clauses = get_number_of_clauses();
        }
        // Add clauses reflecting the operators at the current time step.
        for (OperatorProxy const & operators : task_proxy.get_operators()) {
            int operatorVar = operatorVars[timeStep][operators.get_id()];
            for (FactProxy const & preconditions : operators.get_preconditions()) {
                implies(solver, operatorVar, factsAtTnow[preconditions.get_pair().var][preconditions.get_pair().value]);
            }
            for (EffectProxy const & effects : operators.get_effects()) {
                int effectVar = factsAtTplusOne[effects.get_fact().get_pair().var][effects.get_fact().get_pair().value];
                implies(solver, operatorVar, effectVar);
                // Add frame axiom for the rising flank (neg state becomes pos state)
                frameAxioms[effects.get_fact().get_pair().var][effects.get_fact().get_value()].push_back(operatorVars[timeStep][operators.get_id()]);
            }
        }
        if (timeStep == 0) {
            operator_clauses = get_number_of_clauses()-curr_clauses;
        }

        if (timeStep == 0) {
            curr_clauses = get_number_of_clauses();
        }
        // Add frame axiom clauses.
        for (size_t i=0; i<frameAxioms.size(); i++) {
            for (size_t j=0; j<frameAxioms[i].size(); j++) {
                int neg = factsAtTnow[i][j];
                int pos = factsAtTplusOne[i][j];
                impliesPosAndNegImpliesOr(solver, pos, neg, frameAxioms[i][j]);
            }
        }
        if (timeStep == 0) {
            frame_axioms = get_number_of_clauses()-curr_clauses;
        }

        if (timeStep == 0) {
            curr_clauses = get_number_of_clauses();
        }
        // Add clauses such that exactly one operator can be picked per time step.
        atLeastOne(solver, capsule, operatorVars[timeStep]);
        atMostOne(solver, capsule, operatorVars[timeStep]);
        if (timeStep == 0) {
            operator_limit = get_number_of_clauses()-curr_clauses;
        }

        // At the end of one step prepare the next time step, if it isn't the last.
        if (timeStep == steps-1) {
            break;
        } else {
            sat_step(task_proxy, capsule, factsAtTnow, factsAtTplusOne, operatorVars);
        }
    }

    int curr_clauses = get_number_of_clauses();
    // Add the variables reflecting the goal state of the problem after the last time step.
    for (size_t i=0; i<task_proxy.get_goals().size(); i++) {
        assertYes(solver, factsAtTplusOne[task_proxy.get_goals()[i].get_pair().var][task_proxy.get_goals()[i].get_pair().value]);
    }
    int goal_clauses = get_number_of_clauses()-curr_clauses;

    // Stop encoding timer here.
    enc_timer.stop();
    cout << "[encodingTime=" << enc_timer << "]" << endl;
    cout << capsule.number_of_variables << " variables have been created." << endl;
    cout << get_number_of_clauses() << " clauses have been added." << endl;
    reset_number_of_clauses();
    cout << "[InitClauses=" << init_clauses << "]" << endl;
    cout << "[GoalClauses=" << goal_clauses << "]" << endl;
    cout << "Per time step the following clauses have been added" << endl;
    cout << "[MutexClauses=" << mutex_clauses << "]" << endl;
    cout << "[OperatorClauses=" << operator_clauses << "]" << endl;
    cout << "[FrameAxiomClauses=" << frame_axioms << "]" << endl;
    cout << "[OperatorLimitClauses=" << operator_limit << "]" << endl;
    utils::Timer solution_timer;
    cout << ipasir_solve(solver) << endl;
    solution_timer.stop();
    cout << "[solvingTime=" << solution_timer << "]" << endl;

    // If no plan is found exit the function by returning false and trigger next iteration.
    if (ipasir_solve(solver) == 20) {
        return false;
    }
    
    if (ipasir_solve(solver) == 10){
        // Use plan_manager to save a found plan.
        found_plan(capsule.number_of_variables, task_proxy, solver, operatorVars, false);
        /*
        string validator = "validate";
        string domain_file = "domain.pddl";
        string problem_file = "problem-p01.pddl";
        string plan_file = "found_plan";
        string full_call = validator + " " + domain_file + " " + problem_file + " " + plan_file;
        const char * cmd_call = full_call.c_str();
        int val_return = system(cmd_call);
        if (val_return == 0) {
            return true;
        } else {
            cerr << "ERROR: Calling validator failed!" << endl;
            return true;
        }*/
    }
    // To make compiler shut up.
    return true;
}

bool sat_encoding_binary(TaskProxy task_proxy, int steps) {
    // Start encoding timer here.
    utils::Timer enc_timer;

    /*
    Using two 3D vectors to store the state variables (facts) for the current and
    following time step.
    */
    vector<vector<vector<int>>> binaryFactsAtTnow;
    vector<vector<vector<int>>> binaryFactsAtTplusOne;

    /*
    Using a 2D vector to store the operator variables for each time step.
    Each vector represents the time step at which an operator was executed
    (if true in the returned plan).
    */
    vector<vector<int>> operatorVars;
    void * solver = ipasir_init();
    sat_capsule capsule;
    sat_init_binary(task_proxy, capsule, solver, binaryFactsAtTnow, binaryFactsAtTplusOne, operatorVars);

    // Add the binary variables reflecting the initial state of the problem.
    for (size_t i=0; i<binaryFactsAtTnow.size(); i++) {
        for (size_t j=0; j<binaryFactsAtTnow[i].size(); j++) {
            if ((size_t)task_proxy.get_initial_state().get_values()[i] == j) {
                for (size_t k=0; k<binaryFactsAtTnow[i][j].size(); k++) {
                    // Since polarity of the variables is already embedded in their encoding
                    // they can be inserted as they are.
                    assertYes(solver, binaryFactsAtTnow[i][j][k]);
                }
            }
        }
    }

    for (int timeStep=0; timeStep<steps; timeStep++) {
        // Add clauses reflecting the operators at the current time step.
        for (OperatorProxy const & operators : task_proxy.get_operators()) {
            int operatorVar = operatorVars[timeStep][operators.get_id()];
            for (FactProxy const & preconditions : operators.get_preconditions()) {
                for (size_t i=0; i<binaryFactsAtTnow[preconditions.get_pair().var][preconditions.get_pair().value].size(); i++) {
                    implies(solver, operatorVar, binaryFactsAtTnow[preconditions.get_pair().var][preconditions.get_pair().value][i]);
                }
            }
            for (EffectProxy const & effects : operators.get_effects()) {
                for (size_t i=0; i<binaryFactsAtTplusOne[effects.get_fact().get_pair().var][effects.get_fact().get_pair().value].size(); i++) {
                    implies(solver, operatorVar, binaryFactsAtTplusOne[effects.get_fact().get_pair().var][effects.get_fact().get_pair().value][i]);
                }
            }
        }

        // Vector to collect frame axiom operators.
        vector<vector<vector<int>>> frameAxioms;
        for (size_t i=0; i<binaryFactsAtTnow.size(); i++) {
            vector<vector<int>> variable;
            for (auto j=0; j<=0; j++) {
                for (size_t k=0; k<binaryFactsAtTnow[i][j].size(); k++) {
                    vector<int> upwardFlank;
                    variable.push_back(upwardFlank);
                    vector<int> downwardFlank;
                    variable.push_back(downwardFlank);
                }
            }
        	frameAxioms.push_back(variable);
        }

        // Find all frame axioms.
        for (OperatorProxy const & operators : task_proxy.get_operators()) {
            int operatorVar = operatorVars[timeStep][operators.get_id()];
            for (EffectProxy const & effects : operators.get_effects()) {
                int effVar = effects.get_fact().get_pair().var;
                // TODO: Not sure, if this is the best way to do this?!
                bool matchFound = false;
                for (FactProxy const & preconditions : operators.get_preconditions()) {
                    if (preconditions.get_pair().var == effVar) {
                        matchFound = true;
                        for (size_t i=0; i<binaryFactsAtTnow[effVar][preconditions.get_pair().value].size(); i++) {
                            // Add operator to upward flank vector of fact variable i.
                            if (binaryFactsAtTnow[effVar][preconditions.get_pair().value][i]<0 && 
                                binaryFactsAtTplusOne[effVar][effects.get_fact().get_pair().value][i]>0) {
                                    frameAxioms[effVar][0+2*i].push_back(operatorVar);
                            // Add operator to downward flank vector of fact variable i.
                            } else if (binaryFactsAtTnow[effVar][preconditions.get_pair().value][i]>0 && 
                                binaryFactsAtTplusOne[effVar][effects.get_fact().get_pair().value][i]<0) {
                                    frameAxioms[effVar][1+2*i].push_back(operatorVar);
                            }
                        }
                        // After match is found there's no need to check for more matches.
                        break;
                    }
                }
                if (!matchFound) {
                    // Add operator to downward flank vector of fact variable. Special case when the
                    // effect doesn't have a corresponding precondition in the operator.
                    for (size_t i=0; i<binaryFactsAtTplusOne[effVar][effects.get_fact().get_pair().value].size(); i++) {
                        // Add operator to upward flank vector of fact variable i.
                        if (binaryFactsAtTplusOne[effVar][effects.get_fact().get_pair().value][i]>0) {
                            frameAxioms[effVar][0+2*i].push_back(operatorVar);
                        // Add operator to downward flank vector of fact variable i.
                        } else if (binaryFactsAtTplusOne[effVar][effects.get_fact().get_pair().value][i]<0) {
                            frameAxioms[effVar][1+2*i].push_back(operatorVar);
                        }
                    }
                }
            }
        }
        for (size_t i=0; i<frameAxioms.size(); i++) {
            for (size_t j=0; j<frameAxioms[i].size(); j++) {
                if (j%2 == 0 && frameAxioms[i][j].size()>0) {
                    // upward flank
                    int neg = -binaryFactsAtTnow[i][0][j/2];
                    int pos = -binaryFactsAtTplusOne[i][0][j/2];
                    impliesPosAndNegImpliesOr(solver, pos, neg, frameAxioms[i][j]);
                } else if (j%2 == 1 && frameAxioms[i][j].size()>0) {
                    // downward flank
                    int pos = -binaryFactsAtTnow[i][0][j/2];
                    int neg = -binaryFactsAtTplusOne[i][0][j/2];
                    impliesPosAndNegImpliesOr(solver, pos, neg, frameAxioms[i][j]);
                }
            }
        }

        // Add clauses such that exactly one operator can be picked per time step.
        //atLeastOne(solver, capsule, operatorVars[timeStep]);
        atMostOne(solver, capsule, operatorVars[timeStep]);

        // At the end of one step prepare the next time step, if it isn't the last.
        if (timeStep == steps-1) {
            break;
        } else {
            sat_step_binary(task_proxy, capsule, solver, binaryFactsAtTnow, binaryFactsAtTplusOne, operatorVars);
        }
    }
    // Add the variables reflecting the goal state of the problem after the last time step.
    for (size_t i=0; i<task_proxy.get_goals().size(); i++) {
        for (size_t j=0; j<binaryFactsAtTplusOne[task_proxy.get_goals()[i].get_pair().var][task_proxy.get_goals()[i].get_pair().value].size(); j++) {
            assertYes(solver, binaryFactsAtTplusOne[task_proxy.get_goals()[i].get_pair().var][task_proxy.get_goals()[i].get_pair().value][j]);
        }
    }

    // Stop encoding timer here.
    enc_timer.stop();
    cout << "[encodingTime=" << enc_timer << "]" << endl;
    cout << "That many clauses have been added: " << get_number_of_clauses() << endl;
    reset_number_of_clauses();
    utils::Timer solution_timer;
    cout << ipasir_solve(solver) << endl;
    solution_timer.stop();
    cout << "[solvingTime=" << solution_timer << "]" << endl;

    // If no plan is found exit the function by returning false and trigger next iteration.
    if (ipasir_solve(solver) == 20) {
        return false;
    }
    
    if (ipasir_solve(solver) == 10){
        found_plan(capsule.number_of_variables, task_proxy, solver, operatorVars, true);
        
        string validator = "validate";
        string domain_file = "domain.pddl";
        string problem_file = "problem-p09.pddl";
        string plan_file = "found_plan_binary";
        string full_call = validator + " " + domain_file + " " + problem_file + " " + plan_file;
        const char * cmd_call = full_call.c_str();
        int val_return = system(cmd_call);
        if (val_return == 0) {
            return true;
        } else {
            cerr << "ERROR: Calling validator failed!" << endl;
            return true;
        }
    }
    // To make compiler shut up.
    return true;
}

void sat_forall(TaskProxy task_proxy,
                sat_capsule & capsule,
                vector<vector<int>> & factsAtTnow,
                vector<vector<int>> & operatorVars) {
    
    /*
    Using a 4D vector based on the 2D structure of the fact vectors
    to store operators erasing/requiring a specific fact (state variable).
    */
    vector<vector<vector<vector<int>>>> eraseRequire;

    // Create the structure of the eraseRequire 4D vector.
    for (size_t i=0; i<factsAtTnow.size(); i++) {
        vector<vector<vector<int>>> mutexGroup;
        for (size_t j=0; j<factsAtTnow[i].size(); j++) {
            vector<vector<int>> factVec;
            vector<int> eraseVec;
            vector<int> requireVec;
            factVec.push_back(eraseVec);
            factVec.push_back(requireVec);
            mutexGroup.push_back(factVec);
        }
        eraseRequire.push_back(mutexGroup);
    }

    /*
       TODO: Go through all operators and place them in all the relevant
       erase and require vectors. Require is staight forward: Check precond.
       and put them into the corresponding require vector.
       Erase is tricky because of the mutex property of SAS+ fact groups.
       Idea: Check mutex group of effects, look for corresponding group
       in precond. and put the operator in erase vector of that precond.
       fact. If no precond. of the same group is found, put the operator
       in all erase vectors of all facts of that mutex group except for
       the one I found in effects.
    */
    for (OperatorProxy const & operators : task_proxy.get_operators()) {
        int operatorVar = operators.get_id();
        // Check effects for a corresponding precondition that it erases and
        // add the operator ID to the erase vector of that precondition.
        for (EffectProxy const & effects : operators.get_effects()) {
            int effVar = effects.get_fact().get_pair().var;
            bool matchFound = false;
            for (FactProxy const & preconditions : operators.get_preconditions()) {
                if (preconditions.get_pair().var == effVar) {
                    matchFound = true;
                    // Add operator to erase vector of this precondition.
                    eraseRequire[effVar][preconditions.get_pair().value][0].push_back(operatorVar);
                    break;
                }
            }
            // If no corresponding precondition is found, add the operator ID
            // to all erase vectors of the possible preconditions, except for
            // the fact that becomes true through the operator's effect.
            if(!matchFound) {
                for (size_t i=0; i<eraseRequire[effVar].size(); i++) {
                    if (i != effects.get_fact().get_pair().value) {
                        eraseRequire[effVar][i][0].push_back(operatorVar);
                    }
                }
            }
        }
        // Go through preconditions and add operator ID to all require vectors
        // of the corresponding preconditions.
        for (FactProxy const & preconditions : operators.get_preconditions()) {
            eraseRequire[preconditions.get_pair().var][preconditions.get_pair().value][1].push_back(operatorVar);
        }
    }
    cout << "These are the Em/Rm:\n" << eraseRequire << endl;

}

}
