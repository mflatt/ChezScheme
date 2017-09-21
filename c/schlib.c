/* schlib.c
 * Copyright 1984-2017 Cisco Systems, Inc.
 * 
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "system.h"

/* locally defined functions */
static ptr S_call PROTO((ptr tc, ptr cp, iptr argcnt));

/* Sinteger_value is in number.c */

/* Sinteger32_value is in number.c */

/* Sinteger64_value is in number.c */

void Sset_box(x, y) ptr x, y; {
    SETBOXREF(x, y);
}

void Sset_car(x, y) ptr x, y; {
    SETCAR(x, y);
}

void Sset_cdr(x, y) ptr x, y; {
    SETCDR(x, y);
}

void Svector_set(x, i, y) ptr x; iptr i; ptr y; {
    SETVECTIT(x, i, y);
}

/* Scons is in alloc.c */

ptr Sstring_to_symbol(s) const char *s; {
    return S_intern((const unsigned char *)s);
}

ptr Ssymbol_to_string(x) ptr x; {
  ptr name = SYMNAME(x);
  if (Sstringp(name))
    return name;
  else if (Spairp(name))
    return Scdr(name);
  else
   /* don't have access to prefix or count, and can't handle arbitrary
      prefixes anyway, so always punt */
    return S_string("gensym", -1);
}

/* Sflonum is in alloc.c */

ptr Smake_vector(n, x) iptr n; ptr x; {
    ptr p; iptr i;

    p = S_vector(n);
    for (i = 0; i < n; i += 1) INITVECTIT(p, i) = x;
    return p;
}

ptr Smake_fxvector(n, x) iptr n; ptr x; {
    ptr p; iptr i;

    p = S_fxvector(n);
    for (i = 0; i < n; i += 1) Sfxvector_set(p, i, x);
    return p;
}

ptr Smake_bytevector(n, x) iptr n; int x; {
    ptr p; iptr i;

    p = S_bytevector(n);
    for (i = 0; i < n; i += 1) Sbytevector_u8_set(p, i, (octet)x);
    return p;
}

ptr Smake_string(n, c) iptr n; int c; {
    ptr p; iptr i;

    p = S_string((char *)NULL, n);
    for (i = 0; i < n; i += 1) Sstring_set(p, i, c);
    return p;
}

ptr Smake_uninitialized_string(n) iptr n; {
    return S_string((char *)NULL, n);
}

ptr Sstring(s) const char *s; {
    return S_string(s, -1);
}

ptr Sstring_of_length(s, n) const char *s; iptr n; {
    return S_string(s, n);
}

/* Sbox is in alloc.c */

/* Sinteger is in number.c */

/* Sunsigned is in number.c */

/* Sunsigned32 is in number.c */

/* Sunsigned64 is in number.c */

ptr Stop_level_value(x) ptr x; {
  ptr tc = get_thread_context();
  IBOOL enabled = (DISABLECOUNT(tc) == 0);
  if (enabled) DISABLECOUNT(tc) = FIX(UNFIX(DISABLECOUNT(tc)) + 1);
  x = Scall1(S_symbol_value(Sstring_to_symbol("$c-tlv")), x);
  if (enabled) DISABLECOUNT(tc) = FIX(UNFIX(DISABLECOUNT(tc)) - 1);
  return x;
}

void Sset_top_level_value(x, y) ptr x, y; {
  ptr tc = get_thread_context();
  IBOOL enabled = (DISABLECOUNT(tc) == 0);
  if (enabled) DISABLECOUNT(tc) = FIX(UNFIX(DISABLECOUNT(tc)) + 1);
  Scall2(S_symbol_value(Sstring_to_symbol("$c-stlv!")), x, y);
  if (enabled) DISABLECOUNT(tc) = FIX(UNFIX(DISABLECOUNT(tc)) - 1);
}

#include <setjmp.h>

/* consider rewriting these to avoid multiple calls to get_thread_context */
ptr Scall0(cp) ptr cp; {
    ptr tc = get_thread_context();
    S_initframe(tc,0);
    return S_call(tc, cp, 0);
}

ptr Scall1(cp, x1) ptr cp, x1; {
    ptr tc = get_thread_context();
    S_initframe(tc, 1);
    S_put_arg(tc, 1, x1);
    return S_call(tc, cp, 1);
}

ptr Scall2(cp, x1, x2) ptr cp, x1, x2; {
    ptr tc = get_thread_context();
    S_initframe(tc, 2);
    S_put_arg(tc, 1, x1);
    S_put_arg(tc, 2, x2);
    return S_call(tc, cp, 2);
}

ptr Scall3(cp, x1, x2, x3) ptr cp, x1, x2, x3; {
    ptr tc = get_thread_context();
    S_initframe(tc, 3);
    S_put_arg(tc, 1, x1);
    S_put_arg(tc, 2, x2);
    S_put_arg(tc, 3, x3);
    return S_call(tc, cp, 3);
}

void Sinitframe(n) iptr n; {
    ptr tc = get_thread_context();
    S_initframe(tc, n);
}

void S_initframe(tc, n) ptr tc; iptr n; {
  /* check for and handle stack overflow */
    if ((ptr *)SFP(tc) + n + 2 > (ptr *)ESP(tc))
        S_overflow(tc, (n+2)*sizeof(ptr));

  /* intermediate frame contains old RA + cchain */;
    SFP(tc) = (ptr)((ptr *)SFP(tc) + 2);
}

void Sput_arg(i, x) iptr i; ptr x; {
    ptr tc = get_thread_context();
    S_put_arg(tc, i, x);
}

void S_put_arg(tc, i, x) ptr tc; iptr i; ptr x; {
    if (i <= asm_arg_reg_cnt)
        REGARG(tc, i) = x;
    else
        FRAME(tc, i - asm_arg_reg_cnt) = x;
}

ptr Scall(cp, argcnt) ptr cp; iptr argcnt; {
    ptr tc = get_thread_context();
    return S_call(tc, cp, argcnt);
}

static ptr S_call(tc, cp, argcnt) ptr tc; ptr cp; iptr argcnt; {
    AC0(tc) = (ptr)argcnt;
    AC1(tc) = cp;
    S_call_help(tc, 1);
    return AC0(tc);
}

/* args are set up, argcnt in ac0, closure in ac1 */
void S_call_help(tc, singlep) ptr tc; IBOOL singlep; {
  /* declaring code volatile should be unnecessary, but it quiets gcc */
    void *jb; volatile ptr code;

  /* lock caller's code object, since his return address is sitting in
     the C stack and we may end up in a garbage collection */
    code = CP(tc);
    if (Sprocedurep(code)) code = CLOSCODE(code);
    Slock_object(code);

    CP(tc) = AC1(tc);

    jb = CREATEJMPBUF();
    if (jb == NULL)
      S_error_abort("unable to allocate memory for jump buffer");
    FRAME(tc, -1) = CCHAIN(tc) = Scons(Scons(jb, code), CCHAIN(tc));

    switch (SETJMP(jb)) {
        case 0: /* first time */
            S_generic_invoke(tc, S_G.invoke_code_object);
            S_error_abort("S_generic_invoke return");
            break;
        case -1: /* error */
            S_generic_invoke(tc, S_G.error_invoke_code_object);
            S_error_abort("S_generic_invoke return");
            break;
        case 1: { /* normal return */
            ptr yp = CCHAIN(tc);
            FREEJMPBUF(CAAR(yp));
            CCHAIN(tc) = Scdr(yp);
            break;
        }
        default:
            S_error_abort("unexpected SETJMP return value");
            break;
    }

  /* verify single return value */
    if (singlep && (iptr)AC1(tc) != 1)
        S_error1("", "returned ~s values to single value return context",
                   FIX((iptr)AC1(tc)));

  /* restore caller to cp so that we can lock it again another day.  we
     restore the code object rather than the original closure, as the
     closure may have been relocated or reclaimed by now */
    CP(tc) = code;
}

void S_call_void() {
    ptr tc = get_thread_context();
    S_call_help(tc, 0);
}

ptr S_call_ptr() {
    ptr tc = get_thread_context();
    S_call_help(tc, 1);
    return AC0(tc);
}

iptr S_call_fixnum() {
    ptr tc = get_thread_context();
    S_call_help(tc, 1);
    return Sfixnum_value(AC0(tc));
}

I32 S_call_int32() {
    ptr tc = get_thread_context();
    S_call_help(tc, 1);
    return (I32)Sinteger_value(AC0(tc));
}

U32 S_call_uns32() {
    ptr tc = get_thread_context();
    S_call_help(tc, 1);
    return (U32)Sinteger_value(AC0(tc));
}

I64 S_call_int64() {
    ptr tc = get_thread_context();
    S_call_help(tc, 1);
    return S_int64_value("foreign-callable", AC0(tc));
}

U64 S_call_uns64() {
    ptr tc = get_thread_context();
    S_call_help(tc, 1);
    return S_int64_value("foreign-callable", AC0(tc));
}

double S_call_double() {
    ptr tc = get_thread_context();
    S_call_help(tc, 1);
    return Sflonum_value(AC0(tc));
}

float S_call_single() {
    ptr tc = get_thread_context();
    S_call_help(tc, 1);
    return (float)Sflonum_value(AC0(tc));
}

U8 *S_call_bytevector() {
    ptr tc = get_thread_context();
    S_call_help(tc, 1);
    return (U8 *)&BVIT(AC0(tc),0);
}

uptr S_call_fptr() {
    ptr tc = get_thread_context();
    S_call_help(tc, 1);
    return (uptr)RECORDINSTIT(AC0(tc),0);
}

static void S_call_indirect_help(ptr tc, void *r, iptr sz)
{
    S_call_help(tc, 1);
    memcpy(r, RECORDINSTIT(AC0(tc), 0), sz);
    free(RECORDINSTIT(AC0(tc), 0));
}

char S_call_indirect_byte() {
    ptr tc = get_thread_context();
    char r;
    S_call_indirect_help(tc, &r, sizeof(r));
    return r;
}

short S_call_indirect_short() {
    ptr tc = get_thread_context();
    short r;
    S_call_indirect_help(tc, &r, sizeof(r));
    return r;
}

I32 S_call_indirect_int32() {
    ptr tc = get_thread_context();
    I32 r;
    S_call_indirect_help(tc, &r, sizeof(r));
    return r;
}

I64 S_call_indirect_int64() {
    ptr tc = get_thread_context();
    I64 r;
    S_call_indirect_help(tc, &r, sizeof(r));
    return r;
}

float S_call_indirect_float() {
    ptr tc = get_thread_context();
    float r;
    S_call_indirect_help(tc, &r, sizeof(r));
    return r;
}

double S_call_indirect_double() {
    ptr tc = get_thread_context();
    double r;
    S_call_indirect_help(tc, &r, sizeof(r));
    return r;
}

/* On x86 other than Mac OS, a 1-byte struct covers all configurations
   that don't return in registers and that need to pop the
   result-destination pointer before returning. */
struct result_one_char S_call_indirect_copy_one_char() {
    ptr tc = get_thread_context();
    ptr dest = TS(tc);
    iptr len = UNFIX(TD(tc));
    struct result_one_char r;
    S_call_indirect_help(tc, dest, len);
    memcpy(&r, dest, sizeof(r)); /* will get copied back onto `dest` */
    return r;
}

/* On x86 Mac OS, a 3-byte struct covers all configurations that don't return
   in registers and that need to pop the result-destination pointer
   before returning. */
struct result_three_chars S_call_indirect_copy_three_chars() {
    ptr tc = get_thread_context();
    ptr dest = TS(tc);
    iptr len = UNFIX(TD(tc));
    struct result_three_chars r;
    S_call_indirect_help(tc, dest, len);
    memcpy(&r, dest, sizeof(r)); /* will get copied back onto `dest` */
    return r;
}

/* On x86_64, returns can be returned in up to two integer and/or
   floating-point registers --- but the result may have fewer bytes
   than that, so we pass the actual size and zero-pad the rest. */

struct result_int64_int64 S_call_indirect_sized_int64_int64() {
  ptr tc = get_thread_context();
  iptr len = UNFIX(TD(tc));
  struct result_int64_int64  r = { 0, 0 };
  S_call_indirect_help(tc, &r, len);
  return r;
}

struct result_int64_double S_call_indirect_sized_int64_double() {
  ptr tc = get_thread_context();
  iptr len = UNFIX(TD(tc));
  struct result_int64_double  r = { 0, 0 };
  S_call_indirect_help(tc, &r, len);
  return r;
}

struct result_double_int64 S_call_indirect_sized_double_int64() {
  ptr tc = get_thread_context();
  iptr len = UNFIX(TD(tc));
  struct result_double_int64  r = { 0, 0 };
  S_call_indirect_help(tc, &r, len);
  return r;
}

struct result_double_double S_call_indirect_sized_double_double() {
  ptr tc = get_thread_context();
  iptr len = UNFIX(TD(tc));
  struct result_double_double  r = { 0, 0 };
  S_call_indirect_help(tc, &r, len);
  return r;
}

/* For results not returned in registers on x86_64, coy bytes to the
   result-destination and return that same destination pointer. */
ptr S_call_indirect_copy() {
    ptr tc = get_thread_context();
    ptr dest = TS(tc);
    iptr len = UNFIX(TD(tc));
    S_call_indirect_help(tc, dest, len);
    return dest;
}

/* When a callable receives an argument on the stack to be copied into
   the heap, S_copy_argument() is called to perform the copy. */
void S_copy_argument() {
  ptr tc = get_thread_context();
  ptr x = AC0(tc), x2;
  iptr sz = UNFIX(TS(tc));

  x2 = malloc(sz);
  memcpy(x2, x, sz);

  AC0(tc) = x2;
}

/* cchain = ((jb . co) ...) */
void S_return() {
    ptr tc = get_thread_context();
    ptr xp, yp;

    SFP(tc) = (ptr)((ptr *)SFP(tc) - 2);

  /* grab saved cchain */
    yp = FRAME(tc, 1);

  /* verify saved cchain is sublist of current cchain */
    for (xp = CCHAIN(tc); xp != yp; xp = Scdr(xp))
        if (xp == Snil)
            S_error("", "attempt to return to stale foreign context");

  /* error checks are done; now unlock affected code objects */
    for (xp = CCHAIN(tc); ; xp = Scdr(xp)) {
        Sunlock_object(CDAR(xp));
        if (xp == yp) break;
        FREEJMPBUF(CAAR(xp));
    }

  /* reset cchain and return via longjmp */
    CCHAIN(tc) = yp;
    LONGJMP(CAAR(yp), 1);
}
