#include <sicstus/sicstus.h>

typedef signed short sint;

void           sicstus_write_seq(SP_term_ref);
SP_term_ref    sicstus_increasing_list(sint, sint);
SP_term_ref    sicstus_increasing_list_bounds(sint, sint, sint, sint);
SP_term_ref    sicstus_decreasing_list(sint, sint);
SP_term_ref    sicstus_decreasing_list_bounds(sint, sint, sint, sint);
SP_term_ref    sicstus_increasing_strict_list(sint, sint);
SP_term_ref    sicstus_increasing_strict_list_bounds(sint, sint, sint, sint);
SP_term_ref    sicstus_decreasing_strict_list(sint, sint);
SP_term_ref    sicstus_decreasing_strict_list_bounds(sint, sint, sint, sint);
SP_term_ref    sicstus_alldiff_list(sint, sint);
SP_term_ref    sicstus_alldiff_list_bounds(sint, sint, sint, sint);
void           sicstus_prt_initialize(int, char **);
void           test();
