#ifndef SAT_SAT_H
#define SAT_SAT_H

#include "../ipasir.h"
#include "../tasks/root_task.h"
#include "../task_utils/task_properties.h"
#include "../sat_encoder.h"

#include "../utils/logging.h"

namespace sat {
void sat_solver_call();
void sat_init(TaskProxy task_proxy, sat_capsule & capsule);
void sat_encoding(TaskProxy task_proxy, sat_capsule & capsule);
}
#endif