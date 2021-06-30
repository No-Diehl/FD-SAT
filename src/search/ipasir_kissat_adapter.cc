#include "ipasir.h"
#include "kissat.h"


const char * ipasir_signature (){
	return kissat_signature();
}

void * ipasir_init (){
	return kissat_init();
}

void ipasir_release (void * solver){
	kissat_release((kissat*) solver);
}

void ipasir_add (void * solver, int lit_or_zero){
	kissat_add((kissat*) solver, lit_or_zero);
}

int ipasir_solve (void * solver){
	return kissat_solve((kissat*) solver);
}

int ipasir_val (void * solver, int lit){
	return kissat_value((kissat*) solver, lit);
}
