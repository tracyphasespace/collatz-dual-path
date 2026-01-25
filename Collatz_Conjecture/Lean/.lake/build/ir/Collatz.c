// Lean compiler output
// Module: Collatz
// Imports: Init Mathlib.Data.Nat.Defs Mathlib.Data.Nat.Log Mathlib.Algebra.Ring.Parity Mathlib.Algebra.Order.Field.Basic Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Tactic
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Collatz_three__reaches__one___nativeDecide__1___closed__1;
LEAN_EXPORT lean_object* l_Collatz_E___boxed(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static uint8_t l_Collatz_three__reaches__one___nativeDecide__1___closed__2;
LEAN_EXPORT lean_object* l_Collatz_collatzCompressed(lean_object*);
LEAN_EXPORT lean_object* l_Collatz_collatz(lean_object*);
LEAN_EXPORT lean_object* l___private_Collatz_0__Collatz_trajectory_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Collatz_three__reaches__one___nativeDecide__1;
LEAN_EXPORT lean_object* l_Collatz_trajectory___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Collatz_T(lean_object*);
LEAN_EXPORT lean_object* l___private_Collatz_0__Collatz_trajectory_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l___private_Collatz_0__Collatz_trajectory_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Collatz_collatz___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Collatz_T___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Collatz_E(lean_object*);
LEAN_EXPORT lean_object* l_Collatz_collatzCompressed___boxed(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Collatz_trajectory(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Collatz_E(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_div(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Collatz_E___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Collatz_E(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Collatz_T(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mul(x_2, x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_div(x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Collatz_T___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Collatz_T(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Collatz_collatz(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_mul(x_6, x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_nat_div(x_1, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Collatz_collatz___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Collatz_collatz(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Collatz_collatzCompressed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_mul(x_6, x_1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = lean_nat_div(x_9, x_2);
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_nat_div(x_1, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Collatz_collatzCompressed___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Collatz_collatzCompressed(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Collatz_trajectory(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_Collatz_trajectory(x_1, x_6);
lean_dec(x_6);
x_8 = l_Collatz_collatz(x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Collatz_trajectory___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Collatz_trajectory(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Collatz_0__Collatz_trajectory_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Collatz_0__Collatz_trajectory_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Collatz_0__Collatz_trajectory_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Collatz_0__Collatz_trajectory_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Collatz_0__Collatz_trajectory_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Collatz_three__reaches__one___nativeDecide__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(7u);
x_3 = l_Collatz_trajectory(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_Collatz_three__reaches__one___nativeDecide__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Collatz_three__reaches__one___nativeDecide__1___closed__1;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_Collatz_three__reaches__one___nativeDecide__1() {
_start:
{
uint8_t x_1; 
x_1 = l_Collatz_three__reaches__one___nativeDecide__1___closed__2;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Defs(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Ring_Parity(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Order_Field_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Collatz(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Defs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Ring_Parity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Order_Field_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Collatz_three__reaches__one___nativeDecide__1___closed__1 = _init_l_Collatz_three__reaches__one___nativeDecide__1___closed__1();
lean_mark_persistent(l_Collatz_three__reaches__one___nativeDecide__1___closed__1);
l_Collatz_three__reaches__one___nativeDecide__1___closed__2 = _init_l_Collatz_three__reaches__one___nativeDecide__1___closed__2();
l_Collatz_three__reaches__one___nativeDecide__1 = _init_l_Collatz_three__reaches__one___nativeDecide__1();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
