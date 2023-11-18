/* self-exe.c
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

/*
  This file is meant to be standalone and suitable for use in
  programs other than Chez Scheme.

  SYNOPSIS
    `char *S_get_process_executable_path(const char *exec_file)`

  DESCRIPTION
    `S_get_process_executable_path()` takes `exec_file` (usually
    `argv[0]` supplied to `main()`) and returns the resolved path of
    the containing executable. Searching `exec_file` via `PATH` is
    used as fallback when no platform dependent method is available.
    Memory for the result is obtained with `malloc()`, and can be
    freed with `free()`.

  RETURN VALUE
    On success, `S_get_process_executable_path()` returns a pointer
    to the resolved path string. Otherwise, it returns `NULL`.

  NOTES
    If `SELF_EXE_MAIN` is defined, a `main()` is defined to call and
    print the result from `S_get_process_executable_path`, which is
    useful for testing.

  Parts of the implementation here are from the LLVM Project under
  the Apache License v2.0 with LLVM Exceptions.
*/

#include <stdlib.h>
#include <string.h>

#ifndef WIN32
# if defined(_MSC_VER) || defined(__MINGW32__)
#  define WIN32
# endif
#endif

#ifdef WIN32

#include <windows.h>

static char *wide_to_utf8(const wchar_t *arg) {
  int len = WideCharToMultiByte(CP_UTF8, 0, arg, -1, NULL, 0, NULL, NULL);
  if (0 == len) {
    return NULL;
  }
  char *arg8 = (char *)malloc(len * sizeof(char));
  if (0 == WideCharToMultiByte(CP_UTF8, 0, arg, -1, arg8, len, NULL, NULL)) {
    free(arg8);
    return NULL;
  }
  return arg8;
}

static char *get_process_executable_path(const char *exec_file) {
  wchar_t *path = NULL;
  for (DWORD n = 0, sz = 256;; sz *= 2) {
    path = (wchar_t *)malloc(sz * sizeof(wchar_t));
    n = GetModuleFileNameW(NULL, path, sz);
    if (0 == n) {
      free(path);
      return NULL;
    }
    if (n == sz && GetLastError() == ERROR_INSUFFICIENT_BUFFER) {
      free(path);
    } else {
      break;
    }
  }
  char *r = wide_to_utf8(path);
  free(path);
  return r;
}

#else /* WIN32 */

#include <unistd.h>

/* strdup() is in POSIX, but it's not in C99 */
static char *string_dup(const char *s1)
{
  int l1;
  char *s;
  l1 = strlen(s1);
  s  = (char *)malloc(l1 + 1);
  memcpy(s, s1, l1 + 1);
  return s;
}

/* strtok_r() is not in C99; this function is similar, but only
   has to deal with a single character */
static char *string_char_tok_r(char *in_s, char find, char **state)
{
  int i;

  if (!in_s) in_s = *state;

  if (in_s[0] == 0)
    return NULL;

  for (i = 0; in_s[i] != 0; i++) {
    if (in_s[i] == find) {
      in_s[i] = 0;
      *state = in_s + i + 1;
      return in_s;
    }
  }

  *state = in_s + i;
  return in_s;
}

#if defined(__APPLE__) && defined(__MACH__)
#include <mach-o/dyld.h>
#define HAVE_GET_SELF_PATH_PLATFORM
static char *get_self_path_platform() {
  uint32_t bufsize = 256;
  char *buf = (char *)malloc(bufsize);
  if (_NSGetExecutablePath(buf, &bufsize) == 0) {
    return buf;
  }
  free(buf);
  buf = (char *)malloc(bufsize);
  if (_NSGetExecutablePath(buf, &bufsize) == 0) {
    return buf;
  }
  return NULL;
}
#endif

#if defined(__FreeBSD__)
#define HAVE_GET_SELF_PATH_PLATFORM
#include <errno.h>
#include <osreldate.h>
#if __FreeBSD_version >= 1300057
#include <sys/auxv.h>
#else
#include <machine/elf.h>
extern char **environ;
#endif
static char *get_self_path_platform() {
  /* On FreeBSD if the exec path specified in ELF auxiliary vectors is
     preferred, if available.  /proc/curproc/file and the KERN_PROC_PATHNAME
     sysctl may not return the desired path if there are multiple hardlinks
     to the file. */
#if __FreeBSD_version >= 1300057
  for (size_t bufsize = 256;; bufsize *= 2) {
    char *buf = (char *)malloc(bufsize);
    if (elf_aux_info(AT_EXECPATH, buf, bufsize) == 0) {
      return buf;
    }
    free(buf);
    if (errno != EINVAL) {
      break;
    }
  }
#else
  /* elf_aux_info(AT_EXECPATH, ... is not available in all supported versions,
     fall back to finding the ELF auxiliary vectors after the process's
     environment. */
  char **p = environ;
  while (*p++ != 0)
    ;
  /* Iterate through auxiliary vectors for AT_EXECPATH. */
  for (Elf_Auxinfo *aux = (Elf_Auxinfo *)p; aux->a_type != AT_NULL; aux++) {
    if (aux->a_type == AT_EXECPATH) {
      return string_dup((char *)aux->a_un.a_ptr);
    }
  }
#endif
  return NULL;
}
#endif

#if defined(__sun__) && defined(__svr4__)
#define HAVE_GET_SELF_PATH_PLATFORM
static char *get_self_path_platform() {
  const char *r = getexecname();
  if (r != NULL && strchr(r, '/') != NULL) {
    return string_dup(r);
  }
  return NULL;
}
#endif

#if defined(__linux__) || defined(__CYGWIN__) || defined(__gnu_hurd__)
#define HAVE_GET_SELF_PATH_PLATFORM
static char *get_self_path_platform() { return string_dup("/proc/self/exe"); }
#endif

#if defined(__NetBSD__) || defined(__minix) || defined(__DragonFly__) ||       \
    defined(__FreeBSD_kernel__) || defined(_AIX)
#define HAVE_GET_SELF_PATH_PLATFORM
static char *get_self_path_platform() { return string_dup("/proc/curproc/file"); }
#endif

#ifndef HAVE_GET_SELF_PATH_PLATFORM
static char *get_self_path_platform() { return NULL; }
#endif

static char *path_append(const char *s1, const char *s2) {
  size_t l1 = strlen(s1);
  size_t l2 = strlen(s2);
  char *r = (char *)malloc(l1 + l2 + 2);
  memcpy(r, s1, l1);
  if (r[l1 - 1] != '/') {
    r[l1++] = '/';
  }
  memcpy(r + l1, s2, l2);
  r[l1 + l2] = '\0';
  return r;
}

static char *get_self_path_generic(const char *exec_file) {
  if (strchr(exec_file, '/')) {
    return string_dup(exec_file);
  }
  char *pv = getenv("PATH");
  if (pv == NULL) {
    return NULL;
  }
  char *s = string_dup(pv);
  if (s == NULL) {
    return NULL;
  }
  char *state = NULL;
  for (char *t = string_char_tok_r(s, ':', &state);
       t != NULL;
       t = string_char_tok_r(NULL, ':', &state)) {
    char *r = path_append(t, exec_file);
    if (access(r, X_OK) == 0) {
      free(s);
      return r;
    }
    free(r);
  }
  free(s);
  return NULL;
}

static char *get_process_executable_path(const char *exec_file) {
  char *r = get_self_path_platform();
  if (r == NULL) {
    r = get_self_path_generic(exec_file);
  }
  char *rr = NULL;
  if (r != NULL) {
    rr = realpath(r, NULL);
  }
  free(r);
  return rr;
}

#endif /* WIN32 */

char *S_get_process_executable_path(const char *exec_file) {
  return get_process_executable_path(exec_file);
}

#ifdef SELF_EXE_MAIN
#include <stdio.h>
int main(int argc, char **argv) {
  char *r = S_get_process_executable_path(argv[0]);
  if (r == NULL) {
    r = "Failed to get executable path of current process";
  }
  printf("%s\n", r);
}
#endif
