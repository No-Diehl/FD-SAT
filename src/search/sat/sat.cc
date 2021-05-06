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

/*
Using two 4D vectors based on the 2D structure of the fact
 ectors to store results of the three parts of the chain search.
*/
vector<vector<vector<vector<pair<int,int>>>>> chains;
vector<vector<vector<vector<pair<int,int>>>>> chainsBackwards;

// Storing the sizes of the require vectors.
vector<vector<int>> requireSizes;

// Flag keeping track over sat_forall execution across multiple runs.
bool satForallExecuted = false;

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

void forall_step_to_solver(sat_capsule & capsule,
                           void * solver,
                           const vector<vector<int>> & operatorVars,
                           int timeStep) {
    for (size_t i=0; i<chains.size(); i++) {
        for (size_t j=0; j<chains[i].size(); j++) {
            vector<int> auxVars;
            for (int k=0; k<requireSizes[i][j]; k++) {
                auxVars.push_back(capsule.new_variable());
            }
            //cout << "AuxVars: " << auxVars << endl;
            for (size_t k=0; k<chains[i][j].size(); k++) {
                if (k == 0) {
                    for (size_t l=0; l<chains[i][j][k].size(); l++) {
                        int impLeft = operatorVars[timeStep][chains[i][j][k][l].first];
                        int impRight = auxVars[chains[i][j][k][l].second];
                        //cout << "Inserted forall-step chain starter rule " << impLeft << " -> " << impRight << endl;
                        implies(solver, impLeft, impRight);
                    }
                } else if (k == 1) {
                    for (size_t l=0; l<chains[i][j][k].size(); l++) {
                        int impLeft = auxVars[chains[i][j][k][l].first];
                        int impRight = auxVars[chains[i][j][k][l].second];
                        //cout << "Inserted forall-step chain intersect rule " << impLeft << " -> " << impRight << endl;
                        implies(solver, impLeft, impRight);
                    }
                } else if (k == 2) {
                    for (size_t l=0; l<chains[i][j][k].size(); l++) {
                        int impLeft = auxVars[chains[i][j][k][l].first];
                        int impRight = -operatorVars[timeStep][chains[i][j][k][l].second];
                        //cout << "Inserted forall-step chain end rule " << impLeft << " -> " << impRight << endl;
                        implies(solver, impLeft, impRight);
                    }
                }
            }
        }
    }
    for (size_t i=0; i<chainsBackwards.size(); i++) {
        for (size_t j=0; j<chainsBackwards[i].size(); j++) {
            vector<int> auxVars;
            for (int k=0; k<requireSizes[i][j]; k++) {
                auxVars.push_back(capsule.new_variable());
            }
            for (size_t k=0; k<chainsBackwards[i][j].size(); k++) {
                if (k == 0) {
                    for (size_t l=0; l<chainsBackwards[i][j][k].size(); l++) {
                        int impLeft = operatorVars[timeStep][chainsBackwards[i][j][k][l].first];
                        int impRight = auxVars[chainsBackwards[i][j][k][l].second];
                        //cout << "Inserted forall-step chainBackwards starter rule " << impLeft << " -> " << impRight << endl;
                        implies(solver, impLeft, impRight);
                    }
                } else if (k == 1) {
                    for (size_t l=0; l<chainsBackwards[i][j][k].size(); l++) {
                        int impLeft = auxVars[chainsBackwards[i][j][k][l].first];
                        int impRight = auxVars[chainsBackwards[i][j][k][l].second];
                        //cout << "Inserted forall-step chainBackwards intersect rule " << impLeft << " -> " << impRight << endl;
                        implies(solver, impLeft, impRight);
                    }
                } else if (k == 2) {
                    for (size_t l=0; l<chainsBackwards[i][j][k].size(); l++) {
                        int impLeft = auxVars[chainsBackwards[i][j][k][l].first];
                        int impRight = -operatorVars[timeStep][chainsBackwards[i][j][k][l].second];
                        //cout << "Inserted forall-step chainBackwards end rule " << impLeft << " -> " << impRight << endl;
                        implies(solver, impLeft, impRight);
                    }
                }
            }
        }
    }
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


    vector<vector<set<FactPair>>> mutexes = task_proxy.get_mutex_groups();
    vector<vector<vector<FactPair>>> invariants;

    for (size_t i=0; i<mutexes.size(); i++) {
        vector<vector<FactPair>> group;
        for (size_t j=0; j<mutexes[i].size(); j++) {
            vector<FactPair> variable;
            for (auto it = mutexes[i][j].begin(); it != mutexes[i][j].end(); it++) {
                if (i<(size_t)it->var) {
                    variable.push_back(*it);
                    /*cout << "-" << task_proxy.get_variables()[i].get_fact(j).get_name()
                         << " or -" << task_proxy.get_variables()[it->var].get_fact(it->value).get_name()
                         << endl;*/
                } else if (i==(size_t)it->var && j<(size_t)it->value) {
                    variable.push_back(*it);
                    /*out << "-" << task_proxy.get_variables()[i].get_fact(j).get_name()
                         << " or -" << task_proxy.get_variables()[it->var].get_fact(it->value).get_name()
                         << endl;*/
                }
            }
            group.push_back(variable);
        }
        invariants.push_back(group);
    }

    // @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@DEBUG@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@
    /*
    for (size_t i=0; i<task_proxy.get_variables().size(); i++) {
        cout << "Variable group " << i << ": ";
        for (int j=0; j<task_proxy.get_variables()[i].get_domain_size(); j++) {
            cout << task_proxy.get_variables()[i].get_fact(j).get_name() << "  ";
        }
        cout << endl;
    }
        
    for (OperatorProxy const & operators : task_proxy.get_operators()) {
        cout << "Operator " << operators.get_id() << " is called " << operators.get_name() << ": ";
        for (FactProxy const & preconditions : operators.get_preconditions()) {
            cout << preconditions.get_name() << " (" << preconditions.get_pair() << ") ";
        }
        cout << "--> ";
        for (EffectProxy const & effects : operators.get_effects()) {
            cout << effects.get_fact().get_name() << " (" << effects.get_fact().get_pair() << ") ";
        }
        cout << endl;
    }

    cout << "FactsAtTnow: " << factsAtTnow << endl;
    cout << "FactsAtTplusOne: " << factsAtTplusOne << endl;
    cout << "Operator Vars: " << operatorVars << endl;
    */
    // @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@DEBUG@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

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
    int invariant_clauses = 0;

    for (int timeStep=0; timeStep<steps; timeStep++) {
        //cout << "TIMESTEP IS: " << timeStep << endl;
        // Testing forall encoding preparations.
        if (timeStep == 0 && !satForallExecuted) {
            sat_forall(task_proxy);
            satForallExecuted = true;
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
        //atMostOne(solver, capsule, operatorVars[timeStep]);
        // Replace at-most-one condition with forall_step clauses.
        forall_step_to_solver(capsule, solver, operatorVars, timeStep);

        if (timeStep == 0) {
            operator_limit = get_number_of_clauses()-curr_clauses;
            curr_clauses = get_number_of_clauses();
        }
        // Add invariant clauses to solver.
        for (size_t i=0; i<invariants.size(); i++) {
            if (invariants.size()>0) {
                for (size_t j=0; j<invariants[i].size(); j++) {
                    if (invariants[i][j].size()>0) {
                        for (size_t k=0; k<invariants[i][j].size(); k++) {
                            if (i<(size_t)invariants[i][j][k].var) {
                                impliesNot(solver, factsAtTnow[i][j], factsAtTnow[invariants[i][j][k].var][invariants[i][j][k].value]);
                            } else if (i==(size_t)invariants[i][j][k].var && j<(size_t)invariants[i][j][k].value) {
                                impliesNot(solver, factsAtTnow[i][j], factsAtTnow[invariants[i][j][k].var][invariants[i][j][k].value]);
                            }
                        }
                    }
                }
            }
        }
        if (timeStep == 0) {
            invariant_clauses = get_number_of_clauses()-curr_clauses;
        }

        // At the end of one step prepare the next time step, if it isn't the last.
        if (timeStep == steps-1) {
            // In the very last timestep don't forget to add invariants as well.
            /*for (size_t i=0; i<invariants.size(); i++) {
                if (invariants.size()>0) {
                    for (size_t j=0; j<invariants[i].size(); j++) {
                        if (invariants[i][j].size()>0) {
                            for (size_t k=0; k<invariants[i][j].size(); k++) {
                                if (i<(size_t)invariants[i][j][k].var) {
                                    impliesNot(solver, factsAtTplusOne[i][j], factsAtTplusOne[invariants[i][j][k].var][invariants[i][j][k].value]);
                                } else if (i==(size_t)invariants[i][j][k].var && j<(size_t)invariants[i][j][k].value) {
                                    impliesNot(solver, factsAtTplusOne[i][j], factsAtTplusOne[invariants[i][j][k].var][invariants[i][j][k].value]);
                                }
                            }
                        }
                    }
                }
            }*/
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
    cout << "[InvariantClauses=" << invariant_clauses << "]" << endl;
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
    }
    // To make compiler shut up.
    return true;
}

bool sat_encoding_binary(TaskProxy task_proxy, int steps) {
    // Start encoding timer here.
    utils::Timer enc_timer;

    // Little hack to test forall_step
    vector<vector<int>> factsAtTnow;
    for (size_t i=0; i<task_proxy.get_variables().size(); i++) {
        vector<int> mutexGroupNow;
        for (int j=0; j<task_proxy.get_variables()[i].get_domain_size(); j++) {
            mutexGroupNow.push_back(0);
        }
        factsAtTnow.push_back(mutexGroupNow);
    }

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
        // Testing forall encoding preparations.
        if (timeStep == 0 && !satForallExecuted) {
            sat_forall(task_proxy);
            satForallExecuted = true;
        }

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
        //atMostOne(solver, capsule, operatorVars[timeStep]);
        forall_step_to_solver(capsule, solver, operatorVars, timeStep);

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

void sat_forall(TaskProxy task_proxy) {
    /*
    Using 3D vectors to store operators erasing/requiring
    a specific fact (state variable).
    */
    vector<vector<vector<int>>> eraseGroup;
    vector<vector<vector<int>>> requireGroup;
    vector<vector<vector<int>>> eraseGroupReversed;
    vector<vector<vector<int>>> requireGroupReversed;

    // Storing the sizes of the require vectors of requireGroup.
    vector<vector<int>> requireGroupSizes;

    // Create the structure of chains, eraseGroup and requireGroupSizes
    for (size_t i=0; i<task_proxy.get_variables().size(); i++) {
        vector<vector<vector<pair<int,int>>>> chainGroup;
        vector<vector<int>> mutexGroup;
        // The size vector only needs one vector per mutex group.
        vector<int> mutexGroupSize;
        requireGroupSizes.push_back(mutexGroupSize);
        for (int j=0; j<task_proxy.get_variables()[i].get_domain_size(); j++) {
            // Chains are constructed in three steps, so 3 vectors are needed
            // to store the resulting formula pairs.
            vector<vector<pair<int,int>>> chainVec;
            vector<pair<int,int>> chainStart;
            vector<pair<int,int>> chainIntersect;
            vector<pair<int,int>> chainEnd;
            chainVec.push_back(chainStart);
            chainVec.push_back(chainIntersect);
            chainVec.push_back(chainEnd);
            chainGroup.push_back(chainVec);
            // Per variable a vector is needed to store a list of opertors.
            vector<int> variableVec;
            mutexGroup.push_back(variableVec);
        }
        chains.push_back(chainGroup);
        eraseGroup.push_back(mutexGroup);
    }
    // Copy the structure because it's the same
    requireGroup = eraseGroup;
    eraseGroupReversed = eraseGroup;
    requireGroupReversed = eraseGroup;

    // Same structure needed for the vector with all elements reversed.
    chainsBackwards = chains;

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
                    eraseGroup[effVar][preconditions.get_pair().value].push_back(operatorVar);
                    break;
                }
            }
            // If no corresponding precondition is found, add the operator ID
            // to all erase vectors of the possible preconditions, except for
            // the fact that becomes true through the operator's effect.
            if(!matchFound) {
                for (size_t i=0; i<eraseGroup[effVar].size(); i++) {
                    if (i != (size_t)effects.get_fact().get_pair().value) {
                        eraseGroup[effVar][i].push_back(operatorVar);
                    }
                }
            }
        }
        // Go through preconditions and add operator ID to all require vectors
        // of the corresponding preconditions.
        for (FactProxy const & preconditions : operators.get_preconditions()) {
            requireGroup[preconditions.get_pair().var][preconditions.get_pair().value].push_back(operatorVar);
        }
    }

    // Fill requireGroupSizes with the sizes of their respective vectors
    for (size_t i=0; i<requireGroup.size(); i++) {
        for (size_t j=0; j<requireGroup[i].size(); j++) {
            // If erase and require have only one element which is the same it can
            // safely be deleted to avoid registering unncessary aux variables.
            if (eraseGroup[i][j].size()==1 && requireGroup[i][j].size()==1 &&
                (eraseGroup[i][j][0]==requireGroup[i][j][0])) {
                eraseGroup[i][j].pop_back();
                requireGroup[i][j].pop_back();
            }
            requireGroupSizes[i].push_back(requireGroup[i][j].size());
        }
    }
    requireSizes = requireGroupSizes;
    
    // Construct eraseGroupReversed from eraseGroup
    for (size_t i=0; i<eraseGroup.size(); i++) {
        for (size_t j=0; j<eraseGroup[i].size(); j++) {
            for (size_t k=eraseGroup[i][j].size(); k>0; k--) {
                eraseGroupReversed[i][j].push_back(-eraseGroup[i][j][k-1]);
            }
        }
    }
    // Construct requireGroupReversed from requireGroup
    for (size_t i=0; i<requireGroup.size(); i++) {
        for (size_t j=0; j<requireGroup[i].size(); j++) {
            for (size_t k=requireGroup[i][j].size(); k>0; k--) {
                requireGroupReversed[i][j].push_back(-requireGroup[i][j][k-1]);
            }
        }
    }
    forall_chains(eraseGroup, requireGroup, chains);
    forall_chains(eraseGroupReversed, requireGroupReversed, chainsBackwards);

    /*
    Debugging Code
    cout << "EraseGroup: " << eraseGroup << endl;
    cout << "RequireGroup: " << requireGroup << endl;
    cout << "EraseGroupReversed: " << eraseGroupReversed << endl;
    cout << "RequireGroupReversed: " << requireGroupReversed << endl;
    cout << "requireSizes: " << requireSizes << endl;

    for (size_t i=0; i<chainsBackwards.size(); i++) {
        for (size_t j=0; j<chainsBackwards[i].size(); j++) {
            for (size_t k=0; k<chainsBackwards[i][j][2].size(); k++) {
                cout << "ChainsBackwards[" << i << "][" << j << "][2][" << k << "]=(" <<
                chainsBackwards[i][j][2][k].first << "," << chainsBackwards[i][j][2][k].second << ") ";
            }
            cout << endl;
        }
    }
    */
}

void forall_chains(vector<vector<vector<int>>> & erase,
                    vector<vector<vector<int>>> & require,
                    vector<vector<vector<vector<pair<int,int>>>>> & chainVec) {
    /*
    The chain search consists of three parts:
    1. Chain starters
    2. Chain intersections
    3. Chain ends
    */
    for (size_t i=0; i<erase.size(); i++) {
        for (size_t j=0; j<erase[i].size(); j++) {
            // 1. Chain starters
            size_t firstIndex = 0;
            for (size_t k=0; k<erase[i][j].size(); k++) {
                // Edge case: Require vector is empty
                if (require[i][j].size()<=0) {
                    continue;
                }
                for (size_t l=firstIndex; l<require[i][j].size(); l++) {
                    if (erase[i][j][k]<require[i][j][l]) {
                        // Create rule o^i_t -> a^j,m_t. a^j,m_t represents it's position (index)
                        // inside the require vector. Will be used for replacement with aux var.
                        if (erase[i][j][k]<0) {
                            // Correction for values from reversed vectors.
                            pair<int,int> chainStarter (-erase[i][j][k],l);
                            // Add rule pair to chainStarter vector (index = 0) in chains.
                            chainVec[i][j][0].push_back(chainStarter);
                            //cout << "Added starter rule to chainsBackwards: (op" << erase[i][j][k] << ",a" << l << ")" << endl; 
                            break;
                        } else {
                            pair<int,int> chainStarter (erase[i][j][k],l);
                            // Add rule pair to chainStarter vector (index = 0) in chains.
                            chainVec[i][j][0].push_back(chainStarter);
                            //cout << "Added starter rule to chains: (op" << erase[i][j][k] << ",a" << l << ")" << endl; 
                            break;
                        }
                    } else {
                        firstIndex = l+1;
                    }
                }
            }
            // Edge case: Require vector is empty
            if (require[i][j].size()<=0) {
                continue;
            }
            for (size_t k=0; k<require[i][j].size()-1; k++) {
                if (require[i][j][k]>erase[i][j][0]) {
                    // 2. Chain intersections
                    // Create rule a^i,m_t -> a^j,m_t. Variables represent their position (index)
                    // inside their require vector. Will be used for replacement with aux var.
                    pair<int,int> chainIntersect (k,k+1);
                    // Add rule pair to chainIntersect vector (index = 1).
                    chainVec[i][j][1].push_back(chainIntersect);
                    //cout << "Added intersect rule to chainVec: (a" << k << ",a" << k+1 << ")" << endl;
                    if (require[i][j][k]<0) {
                        // 3. Chain ends
                        // Create rule a^i,m_t -> -o^i_t. a^i,m_t represents it's position (index)
                        // inside the require vector. Will be used for replacement with aux var.
                        // Correction for values from reversed vectors.
                        pair<int,int> chainEnd (k,-require[i][j][k]);
                        chainVec[i][j][2].push_back(chainEnd);
                        //cout << "Added end rule to chainsBackwards: (a" << k << ",-op" << -require[i][j][k] << ")" << endl;
                    } else {
                        pair<int,int> chainEnd (k,require[i][j][k]);
                        // Add rule pair to chainEnd vector (index = 2).
                        chainVec[i][j][2].push_back(chainEnd);
                        //cout << "Added end rule to chains: (a" << k << ",-op" << require[i][j][k] << ")" << endl;
                    }                    
                }
            }
            // End rule for last element of require vector, bc prior for loop ends one index early.
            if (require[i][j][require[i][j].size()-1]>erase[i][j][0]) {
                if (require[i][j][require[i][j].size()-1]<0) {
                    // Correction for values from reversed vectors.
                    pair<int,int> chainEnd ((int)require[i][j].size()-1,-require[i][j][require[i][j].size()-1]);
                    chainVec[i][j][2].push_back(chainEnd);
                    //cout << "Added final end rule to chainsBackwards: (a" << require[i][j].size()-1
                    //     << ",-op" << -require[i][j][require[i][j].size()-1] << ")" << endl;
                } else {
                    pair<int,int> chainEnd ((int)require[i][j].size()-1,require[i][j][require[i][j].size()-1]);
                    chainVec[i][j][2].push_back(chainEnd);
                    //cout << "Added final end rule to chains: (a" << require[i][j].size()-1 
                    //     << ",-op" << require[i][j][require[i][j].size()-1] << ")" << endl;
                }
            }
        }
    }

}

}
