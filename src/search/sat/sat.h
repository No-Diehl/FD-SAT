#ifndef SAT_SAT_H
#define SAT_SAT_H

#include "../ipasir.h"
#include "../plan_manager.h"
#include "../tasks/root_task.h"
#include "../task_utils/task_properties.h"
#include "../sat_encoder.h"
#include "../utils/logging.h"

using namespace std;

namespace sat {
void sat_init(TaskProxy task_proxy, sat_capsule & capsule);
void forbidden_binary_states(vector<vector<vector<int>>> & bF);
void sat_init_binary(TaskProxy task_proxy, sat_capsule & capsule);
void sat_step(TaskProxy task_proxy, sat_capsule & capsule);
void sat_step_binary(TaskProxy task_proxy, sat_capsule & capsule);
void found_plan(int vars, TaskProxy task_proxy, void * solver, const vector<vector<int>> & operatorVars, bool binary);
bool sat_encoding(TaskProxy task_proxy, int steps);
bool sat_encoding_binary(TaskProxy task_proxy, int steps);
}
#endif