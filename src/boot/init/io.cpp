// Lean compiler output
// Module: init.io
// Imports: init.control.state init.control.except init.data.string.basic init.fix
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_io_prim_iterate__aux___main___boxed(obj*, obj*);
obj* l_io_prim_iterate___at_io_prim_iterate__eio___spec__1(obj*, obj*, obj*, obj*);
obj* l_io_fs_handle_mk___rarg(obj*, obj*, obj*, obj*, obj*, uint8, uint8);
obj* l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1(obj*, obj*);
obj* l_io_println___at_io_println_x_27___spec__1(obj*, obj*);
obj* l_io_prim_iterate__aux___boxed(obj*, obj*);
obj* l_from__eio(obj*, obj*);
obj* l_io_print___boxed(obj*, obj*);
obj* l_io_prim_iterate__aux___rarg(obj*, obj*, obj*, obj*);
obj* l_id___boxed(obj*);
obj* l_io_fs_handle_read__to__end___boxed(obj*, obj*);
obj* l_io_prim_lift__eio___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_string_has__to__string___boxed(obj*);
extern "C" obj* lean_io_prim_handle_mk(obj*, uint8, uint8, obj*);
obj* l_io_prim_handle_get__line___boxed(obj*, obj*);
obj* l_io_prim_io__inhabited(obj*);
obj* l_io_fs_handle_flush___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_has__eval___boxed(obj*);
extern obj* l_string_iterator_extract___main___closed__1;
obj* l_io_prim_iterate___at_io_prim_iterate__eio___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_io_prim_handle_flush___boxed(obj*, obj*);
obj* l_io_fs_handle_is__eof___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_io_has__eval(obj*);
obj* l_has__repr_has__eval___rarg(obj*, obj*, obj*);
obj* l_io_fs_handle_close___boxed(obj*, obj*);
obj* l_io_prim_iterate___rarg(obj*, obj*, obj*);
obj* l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__2___boxed(obj*, obj*);
obj* l_io_has__eval___rarg(obj*, obj*, obj*);
obj* l_eio__unit_has__eval___boxed(obj*);
extern "C" obj* lean_io_prim_put_str(obj*, obj*);
obj* l_io_fs_handle_flush(obj*, obj*);
obj* l_io_prim_lift__eio___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_get__line___boxed(obj*);
obj* l_io_prim_handle_is__eof___boxed(obj*, obj*);
obj* l_io_prim_iterate___at_io_prim_iterate__eio___spec__1___rarg(obj*, obj*, obj*);
obj* l_io_prim_handle_mk___boxed(obj*, obj*, obj*, obj*);
obj* l_io_fs_read__file___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_io_prim_lift__eio(obj*, obj*, obj*);
obj* l_io_prim_io__inhabited___boxed(obj*);
obj* l___private_init_io_12__put__str___at_io_println___spec__1(obj*, obj*);
obj* l___private_init_io_12__put__str___at_io_println_x_27___spec__3(obj*, obj*);
obj* l_io_fs_handle_mk___boxed(obj*, obj*);
obj* l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1___boxed(obj*, obj*);
obj* l___private_init_io_12__put__str(obj*, obj*);
obj* l_io_println_x_27___boxed(obj*, obj*);
obj* l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__2(obj*, obj*);
obj* l_io_println___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_io_12__put__str___at_io_println_x_27___spec__3___boxed(obj*, obj*);
obj* l_io_print___at_io_println_x_27___spec__2___boxed(obj*, obj*);
obj* l_io_fs_handle_get__line___boxed(obj*, obj*);
obj* l_io_fs_handle_is__eof___rarg(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_eio_has__eval(obj*, obj*);
obj* l_io_print___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_io_12__put__str___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_fs_read__file___boxed(obj*, obj*);
obj* l_io_fs_handle_is__eof___boxed(obj*, obj*);
obj* l_io_fs_read__file___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_io_fs_handle_read__to__end(obj*, obj*);
obj* l_io_prim_put__str___boxed(obj*, obj*);
obj* l___private_init_io_12__put__str___boxed(obj*, obj*);
obj* l_io_prim_iterate__eio___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_io_12__put__str___at_io_println___spec__1___boxed(obj*, obj*);
obj* l_io_prim_iterate__eio___boxed(obj*, obj*, obj*);
obj* l_io_error_has__to__string;
obj* l_io_prim_io__inhabited___rarg(obj*);
obj* l_io_fs_read__file___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_io_prim_handle_close(obj*, obj*);
obj* l_io_lazy__pure___boxed(obj*);
obj* l_io_prim_inhabited(obj*, obj*);
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_io_println___boxed(obj*, obj*);
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1(obj*, obj*);
obj* l_io_prim_iterate(obj*, obj*, obj*);
obj* l_io_prim_iterate___boxed(obj*, obj*, obj*);
obj* l_io_prim_iterate__eio___rarg(obj*, obj*, obj*, obj*);
obj* l_has__repr_has__eval(obj*);
obj* l_io_println___rarg___closed__1;
obj* l_io_print(obj*, obj*);
obj* l_io_fs_handle_is__eof(obj*, obj*);
obj* l_io_prim_iterate___at_io_prim_iterate__eio___spec__1___rarg___lambda__1(obj*, obj*, obj*);
obj* l_io_prim_inhabited___rarg(obj*);
obj* l_io_fs_handle_close___rarg(obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_io_prim_handle_flush(obj*, obj*);
obj* l_io_fs_read__file___rarg___lambda__1(obj*, obj*, obj*);
obj* l_io_monad;
obj* l_io_println___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_state__t_pure___at_io_prim_io__inhabited___spec__1___rarg(obj*, obj*);
obj* l_id_monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l_eio__unit_has__eval(obj*);
obj* l_has__repr_has__eval___boxed(obj*);
obj* l_eio_has__eval___rarg(obj*, obj*, obj*, obj*);
extern "C" obj* lean_io_prim_get_line(obj*);
obj* l_string_has__lift___boxed(obj*);
obj* l_io_prim_iterate___at_io_fs_handle_read__to__end___spec__4___lambda__1(obj*, obj*, obj*);
obj* l_io_fs_handle_get__line___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_eio__unit_has__eval___rarg(obj*, obj*, obj*);
obj* l_io_prim_iterate__aux(obj*, obj*);
extern "C" obj* lean_io_unsafe(obj*, obj*);
obj* l_io_fs_read__file(obj*, obj*);
obj* l___private_init_io_12__put__str___at_io_println___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_lift__eio___boxed(obj*, obj*, obj*);
obj* l_io_fs_handle_flush___boxed(obj*, obj*);
obj* l_state__t_pure___at_io_prim_io__inhabited___spec__1(obj*);
extern "C" obj* lean_io_prim_handle_get_line(obj*, obj*);
obj* l_unsafe__io___boxed(obj*, obj*);
obj* l_io_lazy__pure(obj*);
obj* l_io_fs_handle_mk(obj*, obj*);
obj* l_io_fs_read__file___rarg___lambda__1___boxed(obj*, obj*, obj*);
obj* l_io_println_x_27(obj*, obj*);
obj* l_io_lazy__pure___rarg(obj*, obj*);
obj* l_io_error_inhabited;
obj* l_io_fs_handle_read__to__end___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_handle_close___boxed(obj*, obj*);
obj* l_io_prim_iterate___at_io_fs_handle_read__to__end___spec__4(obj*, obj*);
obj* l_id_bind___boxed(obj*, obj*);
obj* l_io_prim_iterate__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate___at_io_fs_handle_read__to__end___spec__4___lambda__1___boxed(obj*, obj*, obj*);
obj* l_io_println(obj*, obj*);
obj* l_io_print___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_timeit___boxed(obj*, obj*, obj*, obj*);
obj* l_io_print___at_io_println_x_27___spec__2(obj*, obj*);
obj* l_io_fs_handle_mk___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern "C" obj* lean_io_timeit(obj*, obj*, obj*, obj*);
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, uint8, uint8);
obj* l_io_prim_inhabited___boxed(obj*, obj*);
obj* l_io_fs_handle_close(obj*, obj*);
obj* l_io_println___at_io_println_x_27___spec__1___boxed(obj*, obj*);
obj* l_io__unit_has__eval(obj*, obj*);
obj* l_state__t_pure___at_io_prim_io__inhabited___spec__1___boxed(obj*);
extern "C" obj* lean_io_prim_handle_is_eof(obj*, obj*);
obj* l_eio_has__eval___boxed(obj*, obj*);
obj* l_eio_has__eval___rarg___closed__1;
obj* l_id_monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_string_has__lift(obj*);
obj* l_io_fs_handle_get__line(obj*, obj*);
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1___boxed(obj*, obj*);
obj* l_id_monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate__eio___at_io_fs_handle_read__to__end___spec__3(obj*, obj*);
obj* l_io_prim_iterate__aux___main(obj*, obj*);
obj* l_io_fs_read__file___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_io_prim_iterate__eio(obj*, obj*, obj*);
obj* _init_l_io_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_state__t_monad___rarg(x_9);
return x_10;
}
}
obj* l_unsafe__io___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_unsafe(x_0, x_1);
return x_2;
}
}
obj* l_timeit___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean_io_timeit(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_io_error_has__to__string() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_string_has__to__string___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_io_error_inhabited() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("");
return x_0;
}
}
obj* l_string_has__lift(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_string_has__lift___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_string_has__lift(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_io_lazy__pure___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = lean::box(0);
x_3 = lean::apply_1(x_0, x_2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
}
obj* l_io_lazy__pure(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_io_lazy__pure___rarg), 2, 0);
return x_1;
}
}
obj* l_io_lazy__pure___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_io_lazy__pure(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_io_prim_iterate__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_2(x_0, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_13; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::apply_2(x_1, x_10, x_7);
return x_13;
}
else
{
obj* x_15; obj* x_17; obj* x_18; obj* x_21; 
lean::dec(x_1);
x_15 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_17 = x_4;
} else {
 lean::inc(x_15);
 lean::dec(x_4);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_5, 0);
lean::inc(x_18);
lean::dec(x_5);
if (lean::is_scalar(x_17)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_17;
}
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_15);
return x_21;
}
}
}
obj* l_io_prim_iterate__aux___main(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__aux___main___rarg), 4, 0);
return x_2;
}
}
obj* l_io_prim_iterate__aux___main___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_prim_iterate__aux___main(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_prim_iterate__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_io_prim_iterate__aux___main___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_io_prim_iterate__aux(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__aux___rarg), 4, 0);
return x_2;
}
}
obj* l_io_prim_iterate__aux___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_prim_iterate__aux(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_state__t_pure___at_io_prim_io__inhabited___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_state__t_pure___at_io_prim_io__inhabited___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_pure___at_io_prim_io__inhabited___spec__1___rarg), 2, 0);
return x_1;
}
}
obj* l_io_prim_io__inhabited___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_pure___at_io_prim_io__inhabited___spec__1___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_io_prim_io__inhabited(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_io__inhabited___rarg), 1, 0);
return x_1;
}
}
obj* l_state__t_pure___at_io_prim_io__inhabited___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_state__t_pure___at_io_prim_io__inhabited___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_io_prim_io__inhabited___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_io_prim_io__inhabited(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_io_prim_iterate___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__aux___rarg), 4, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::fixpoint2(x_3, x_0, x_2);
return x_4;
}
}
obj* l_io_prim_iterate(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___rarg), 3, 0);
return x_3;
}
}
obj* l_io_prim_iterate___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_inhabited___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_io_prim_inhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_inhabited___rarg), 1, 0);
return x_2;
}
}
obj* l_io_prim_inhabited___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_prim_inhabited(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_prim_iterate___at_io_prim_iterate__eio___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_2(x_0, x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_8 = x_3;
} else {
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_6);
return x_14;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 x_17 = x_4;
} else {
 lean::inc(x_15);
 lean::dec(x_4);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_17);
x_19 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_21 = x_3;
} else {
 lean::inc(x_19);
 lean::dec(x_3);
 x_21 = lean::box(0);
}
x_22 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_24 = x_15;
} else {
 lean::inc(x_22);
 lean::dec(x_15);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_21)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_21;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_19);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_27 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_29 = x_3;
} else {
 lean::inc(x_27);
 lean::dec(x_3);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_32 = x_15;
} else {
 lean::inc(x_30);
 lean::dec(x_15);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_17;
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
if (lean::is_scalar(x_29)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_29;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_27);
return x_35;
}
}
}
}
obj* l_io_prim_iterate___at_io_prim_iterate__eio___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_io_prim_iterate__eio___spec__1___rarg___lambda__1), 3, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__aux___rarg), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::fixpoint2(x_4, x_0, x_2);
return x_5;
}
}
obj* l_io_prim_iterate___at_io_prim_iterate__eio___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_io_prim_iterate__eio___spec__1___rarg), 3, 0);
return x_4;
}
}
obj* l_io_prim_iterate__eio___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_io_prim_iterate___at_io_prim_iterate__eio___spec__1___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_io_prim_iterate__eio(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__eio___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_io_prim_iterate___at_io_prim_iterate__eio___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_io_prim_iterate___at_io_prim_iterate__eio___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_io_prim_iterate__eio___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_io_prim_iterate__eio___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_io_prim_iterate__eio___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate__eio(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_prim_put__str___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_put_str(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_prim_get__line___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean_io_prim_get_line(x_0);
return x_1;
}
}
obj* l_io_prim_handle_mk___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; uint8 x_5; obj* x_6; 
x_4 = lean::unbox(x_1);
x_5 = lean::unbox(x_2);
x_6 = lean_io_prim_handle_mk(x_0, x_4, x_5, x_3);
lean::dec(x_0);
return x_6;
}
}
obj* l_io_prim_handle_is__eof___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_handle_is_eof(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_prim_handle_flush___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_handle_flush(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_prim_handle_close___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_handle_close(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_prim_handle_get__line___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean_io_prim_handle_get_line(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_prim_lift__eio___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::apply_1(x_1, x_5);
x_12 = lean::apply_2(x_8, lean::box(0), x_11);
return x_12;
}
else
{
obj* x_15; obj* x_18; obj* x_21; obj* x_24; 
lean::dec(x_1);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::apply_2(x_21, lean::box(0), x_15);
return x_24;
}
}
}
obj* l_io_prim_lift__eio___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_3, 1);
lean::inc(x_5);
x_7 = lean::apply_2(x_0, lean::box(0), x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_3);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_io_prim_lift__eio(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg), 5, 0);
return x_3;
}
}
obj* l_io_prim_lift__eio___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_lift__eio(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l___private_init_io_12__put__str___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_put__str___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::apply_2(x_0, lean::box(0), x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l___private_init_io_12__put__str(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_io_12__put__str___rarg), 5, 0);
return x_2;
}
}
obj* l___private_init_io_12__put__str___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_12__put__str(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_print___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::apply_1(x_5, x_6);
x_8 = l___private_init_io_12__put__str___rarg(x_0, x_1, x_2, x_3, x_7);
return x_8;
}
}
obj* l_io_print(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_print___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_io_print___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_io_print___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
return x_7;
}
}
obj* l_io_print___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_print(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_io_12__put__str___at_io_println___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_put__str___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::apply_2(x_0, lean::box(0), x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l___private_init_io_12__put__str___at_io_println___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_io_12__put__str___at_io_println___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* _init_l_io_println___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\n");
return x_0;
}
}
obj* l_io_println___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_7 = lean::cnstr_get(x_3, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_7, 4);
lean::inc(x_9);
lean::dec(x_7);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_16 = l_io_print___rarg(x_0, x_1, x_2, x_3, lean::box(0), x_5, x_6);
x_17 = l_io_println___rarg___closed__1;
x_18 = l___private_init_io_12__put__str___at_io_println___spec__1___rarg(x_0, x_1, x_2, x_3, x_17);
x_19 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_16, x_18);
return x_19;
}
}
obj* l_io_println(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_println___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l___private_init_io_12__put__str___at_io_println___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_12__put__str___at_io_println___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_println___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_io_println___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
return x_7;
}
}
obj* l_io_println___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_println(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_fs_handle_mk___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5, uint8 x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::box(x_5);
x_8 = lean::box(x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_handle_mk___boxed), 4, 3);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_7);
lean::closure_set(x_9, 2, x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
x_12 = lean::apply_2(x_0, lean::box(0), x_9);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_3);
x_14 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_io_fs_handle_mk(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_mk___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_io_fs_handle_mk___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; uint8 x_8; obj* x_9; 
x_7 = lean::unbox(x_5);
x_8 = lean::unbox(x_6);
x_9 = l_io_fs_handle_mk___rarg(x_0, x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
obj* l_io_fs_handle_mk___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_fs_handle_mk(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_fs_handle_is__eof___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::apply_1(x_1, x_5);
x_12 = lean::apply_2(x_8, lean::box(0), x_11);
return x_12;
}
else
{
obj* x_15; obj* x_18; obj* x_21; obj* x_24; 
lean::dec(x_1);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_18 = lean::cnstr_get(x_2, 0);
lean::inc(x_18);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::apply_2(x_21, lean::box(0), x_15);
return x_24;
}
}
}
obj* l_io_fs_handle_is__eof___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_handle_is__eof___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::apply_2(x_0, lean::box(0), x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_is__eof___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_io_fs_handle_is__eof(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_is__eof___rarg), 5, 0);
return x_2;
}
}
obj* l_io_fs_handle_is__eof___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_fs_handle_is__eof(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_fs_handle_flush___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_handle_flush___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::apply_2(x_0, lean::box(0), x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_io_fs_handle_flush(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_flush___rarg), 5, 0);
return x_2;
}
}
obj* l_io_fs_handle_flush___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_fs_handle_flush(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_fs_handle_close___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_handle_flush___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::apply_2(x_0, lean::box(0), x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_io_fs_handle_close(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_close___rarg), 5, 0);
return x_2;
}
}
obj* l_io_fs_handle_close___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_fs_handle_close(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_fs_handle_get__line___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_handle_get__line___boxed), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::apply_2(x_0, lean::box(0), x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_io_fs_handle_get__line(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_get__line___rarg), 5, 0);
return x_2;
}
}
obj* l_io_fs_handle_get__line___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_fs_handle_get__line(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean_io_prim_handle_is_eof(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
} else {
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_15 = x_2;
} else {
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_18 = x_3;
} else {
 lean::inc(x_16);
 lean::dec(x_3);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
return x_20;
}
}
}
obj* l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean_io_prim_handle_get_line(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
} else {
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_15 = x_2;
} else {
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_18 = x_3;
} else {
 lean::inc(x_16);
 lean::dec(x_3);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
return x_20;
}
}
}
obj* l_io_prim_iterate___at_io_fs_handle_read__to__end___spec__4___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_6 = l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1(x_0, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::dec(x_6);
x_13 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_15 = x_7;
} else {
 lean::inc(x_13);
 lean::dec(x_7);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
x_3 = x_16;
x_4 = x_10;
goto lbl_5;
}
else
{
obj* x_17; obj* x_19; uint8 x_20; 
x_17 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 x_19 = x_7;
} else {
 lean::inc(x_17);
 lean::dec(x_7);
 x_19 = lean::box(0);
}
x_20 = lean::unbox(x_17);
if (x_20 == 0)
{
obj* x_22; obj* x_25; obj* x_26; 
lean::dec(x_19);
x_22 = lean::cnstr_get(x_6, 1);
lean::inc(x_22);
lean::dec(x_6);
x_25 = l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__2(x_0, x_22);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_29 = lean::cnstr_get(x_25, 1);
lean::inc(x_29);
lean::dec(x_25);
x_32 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_34 = x_26;
} else {
 lean::inc(x_32);
 lean::dec(x_26);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
x_3 = x_35;
x_4 = x_29;
goto lbl_5;
}
else
{
obj* x_36; obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
x_36 = lean::cnstr_get(x_25, 1);
lean::inc(x_36);
lean::dec(x_25);
x_39 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_41 = x_26;
} else {
 lean::inc(x_39);
 lean::dec(x_26);
 x_41 = lean::box(0);
}
x_42 = lean::string_append(x_1, x_39);
lean::dec(x_39);
x_44 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_44, 0, x_42);
if (lean::is_scalar(x_41)) {
 x_45 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_45 = x_41;
}
lean::cnstr_set(x_45, 0, x_44);
x_3 = x_45;
x_4 = x_36;
goto lbl_5;
}
}
else
{
obj* x_46; obj* x_49; obj* x_50; 
x_46 = lean::cnstr_get(x_6, 1);
lean::inc(x_46);
lean::dec(x_6);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_1);
if (lean::is_scalar(x_19)) {
 x_50 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_50 = x_19;
}
lean::cnstr_set(x_50, 0, x_49);
x_3 = x_50;
x_4 = x_46;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_51 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_53 = x_3;
} else {
 lean::inc(x_51);
 lean::dec(x_3);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_4);
return x_56;
}
else
{
obj* x_57; obj* x_59; 
x_57 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 x_59 = x_3;
} else {
 lean::inc(x_57);
 lean::dec(x_3);
 x_59 = lean::box(0);
}
if (lean::obj_tag(x_57) == 0)
{
obj* x_61; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_59);
x_61 = lean::cnstr_get(x_57, 0);
if (lean::is_exclusive(x_57)) {
 x_63 = x_57;
} else {
 lean::inc(x_61);
 lean::dec(x_57);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_61);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_4);
return x_65;
}
else
{
obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_66 = lean::cnstr_get(x_57, 0);
if (lean::is_exclusive(x_57)) {
 x_68 = x_57;
} else {
 lean::inc(x_66);
 lean::dec(x_57);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_59;
}
lean::cnstr_set(x_69, 0, x_66);
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_4);
return x_71;
}
}
}
}
}
obj* l_io_prim_iterate___at_io_fs_handle_read__to__end___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate___at_io_fs_handle_read__to__end___spec__4___lambda__1___boxed), 3, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__aux___rarg), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_string_iterator_extract___main___closed__1;
x_5 = lean::fixpoint2(x_3, x_4, x_1);
return x_5;
}
}
obj* l_io_prim_iterate__eio___at_io_fs_handle_read__to__end___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_prim_iterate___at_io_fs_handle_read__to__end___spec__4(x_0, x_1);
return x_2;
}
}
obj* l_io_fs_handle_read__to__end___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_iterate__eio___at_io_fs_handle_read__to__end___spec__3), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::apply_2(x_0, lean::box(0), x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_2);
lean::closure_set(x_9, 2, x_3);
x_10 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_io_fs_handle_read__to__end(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_read__to__end___rarg), 5, 0);
return x_2;
}
}
obj* l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_fs_handle_is__eof___at_io_fs_handle_read__to__end___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_fs_handle_get__line___at_io_fs_handle_read__to__end___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_prim_iterate___at_io_fs_handle_read__to__end___spec__4___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_prim_iterate___at_io_fs_handle_read__to__end___spec__4___lambda__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_io_fs_handle_read__to__end___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_fs_handle_read__to__end(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5, uint8 x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::box(x_5);
x_8 = lean::box(x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_handle_mk___boxed), 4, 3);
lean::closure_set(x_9, 0, x_4);
lean::closure_set(x_9, 1, x_7);
lean::closure_set(x_9, 2, x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
x_12 = lean::apply_2(x_0, lean::box(0), x_9);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_io_prim_lift__eio___rarg___lambda__1), 4, 3);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_3);
x_14 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_io_fs_read__file___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_2(x_6, lean::box(0), x_1);
return x_9;
}
}
obj* l_io_fs_read__file___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_3);
x_8 = l_io_fs_handle_close___rarg(x_0, x_1, x_2, x_3, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_read__file___rarg___lambda__1___boxed), 3, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_6);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_io_fs_read__file___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_11; obj* x_13; obj* x_14; 
lean::inc(x_5);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_io_fs_handle_read__to__end___rarg(x_0, x_1, x_2, x_3, x_5);
lean::inc(x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_read__file___rarg___lambda__2), 7, 6);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_3);
lean::closure_set(x_13, 4, x_5);
lean::closure_set(x_13, 5, x_4);
x_14 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_11, x_13);
return x_14;
}
}
obj* l_io_fs_read__file___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; uint8 x_8; obj* x_13; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = 0;
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_13 = l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_8, x_5);
lean::inc(x_6);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_read__file___rarg___lambda__3), 6, 5);
lean::closure_set(x_15, 0, x_0);
lean::closure_set(x_15, 1, x_1);
lean::closure_set(x_15, 2, x_2);
lean::closure_set(x_15, 3, x_3);
lean::closure_set(x_15, 4, x_6);
x_16 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_13, x_15);
return x_16;
}
}
obj* l_io_fs_read__file(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_io_fs_read__file___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; uint8 x_8; obj* x_9; 
x_7 = lean::unbox(x_5);
x_8 = lean::unbox(x_6);
x_9 = l_io_fs_handle_mk___at_io_fs_read__file___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
}
obj* l_io_fs_handle_mk___at_io_fs_read__file___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_fs_handle_mk___at_io_fs_read__file___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_io_fs_read__file___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_io_fs_read__file___rarg___lambda__1(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_io_fs_read__file___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_io_fs_read__file___rarg(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_io_fs_read__file___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_fs_read__file(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_from__eio(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::apply_1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
}
obj* l___private_init_io_12__put__str___at_io_println_x_27___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean_io_prim_put_str(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
} else {
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_15 = x_2;
} else {
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_18 = x_3;
} else {
 lean::inc(x_16);
 lean::dec(x_3);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
return x_20;
}
}
}
obj* l_io_print___at_io_println_x_27___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_12__put__str___at_io_println_x_27___spec__3(x_0, x_1);
return x_2;
}
}
obj* l_io_println___at_io_println_x_27___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l___private_init_io_12__put__str___at_io_println_x_27___spec__3(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_7 = x_2;
} else {
 lean::inc(x_5);
 lean::dec(x_2);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
if (lean::is_scalar(x_10)) {
 x_11 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_11 = x_10;
}
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_7)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_7;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::dec(x_2);
x_17 = l_io_println___rarg___closed__1;
x_18 = l___private_init_io_12__put__str___at_io_println_x_27___spec__3(x_17, x_14);
return x_18;
}
}
}
obj* l_io_println_x_27(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_2 = l_io_println___at_io_println_x_27___spec__1(x_0, x_1);
x_3 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_5 = x_2;
} else {
 lean::inc(x_3);
 lean::dec(x_2);
 x_5 = lean::box(0);
}
x_6 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
}
obj* l___private_init_io_12__put__str___at_io_println_x_27___spec__3___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_io_12__put__str___at_io_println_x_27___spec__3(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_print___at_io_println_x_27___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_print___at_io_println_x_27___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_println___at_io_println_x_27___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_println___at_io_println_x_27___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_io_println_x_27___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_io_println_x_27(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_has__repr_has__eval___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_0, x_1);
x_4 = l_io_println_x_27(x_3, x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_has__repr_has__eval(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_has__repr_has__eval___rarg), 3, 0);
return x_1;
}
}
obj* l_has__repr_has__eval___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_has__repr_has__eval(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_io_has__eval___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_9; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_2(x_0, x_4, x_6);
return x_9;
}
}
obj* l_io_has__eval(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_io_has__eval___rarg), 3, 0);
return x_1;
}
}
obj* l_io_has__eval___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_io_has__eval(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_io__unit_has__eval(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::apply_1(x_0, x_1);
return x_2;
}
}
obj* _init_l_eio_has__eval___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("Error: ");
return x_0;
}
}
obj* l_eio_has__eval___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_18; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
lean::dec(x_5);
x_14 = lean::apply_1(x_0, x_11);
x_15 = l_eio_has__eval___rarg___closed__1;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = l_io_println_x_27(x_16, x_8);
lean::dec(x_16);
return x_18;
}
else
{
obj* x_21; obj* x_24; obj* x_27; 
lean::dec(x_0);
x_21 = lean::cnstr_get(x_4, 1);
lean::inc(x_21);
lean::dec(x_4);
x_24 = lean::cnstr_get(x_5, 0);
lean::inc(x_24);
lean::dec(x_5);
x_27 = lean::apply_2(x_1, x_24, x_21);
return x_27;
}
}
}
obj* l_eio_has__eval(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_eio_has__eval___rarg), 4, 0);
return x_2;
}
}
obj* l_eio_has__eval___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_eio_has__eval(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_eio__unit_has__eval___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::apply_1(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::apply_1(x_0, x_9);
x_13 = l_eio_has__eval___rarg___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = l_io_println_x_27(x_14, x_6);
lean::dec(x_14);
return x_16;
}
else
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_4);
lean::dec(x_0);
x_20 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_22 = x_3;
} else {
 lean::inc(x_20);
 lean::dec(x_3);
 x_22 = lean::box(0);
}
x_23 = lean::box(0);
if (lean::is_scalar(x_22)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_22;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_20);
return x_24;
}
}
}
obj* l_eio__unit_has__eval(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_eio__unit_has__eval___rarg), 3, 0);
return x_1;
}
}
obj* l_eio__unit_has__eval___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_eio__unit_has__eval(x_0);
lean::dec(x_0);
return x_1;
}
}
void initialize_init_control_state();
void initialize_init_control_except();
void initialize_init_data_string_basic();
void initialize_init_fix();
static bool _G_initialized = false;
void initialize_init_io() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_control_state();
 initialize_init_control_except();
 initialize_init_data_string_basic();
 initialize_init_fix();
 l_io_monad = _init_l_io_monad();
lean::mark_persistent(l_io_monad);
 l_io_error_has__to__string = _init_l_io_error_has__to__string();
lean::mark_persistent(l_io_error_has__to__string);
 l_io_error_inhabited = _init_l_io_error_inhabited();
lean::mark_persistent(l_io_error_inhabited);
 l_io_println___rarg___closed__1 = _init_l_io_println___rarg___closed__1();
lean::mark_persistent(l_io_println___rarg___closed__1);
 l_eio_has__eval___rarg___closed__1 = _init_l_eio_has__eval___rarg___closed__1();
lean::mark_persistent(l_eio_has__eval___rarg___closed__1);
}
