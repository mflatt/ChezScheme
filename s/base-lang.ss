;;; base-lang.ss
;;; Copyright 1984-2017 Cisco Systems, Inc.
;;; 
;;; Licensed under the Apache License, Version 2.0 (the "License");
;;; you may not use this file except in compliance with the License.
;;; You may obtain a copy of the License at
;;; 
;;; http://www.apache.org/licenses/LICENSE-2.0
;;; 
;;; Unless required by applicable law or agreed to in writing, software
;;; distributed under the License is distributed on an "AS IS" BASIS,
;;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;;; See the License for the specific language governing permissions and
;;; limitations under the License.

(module (Lsrc Lsrc? Ltype Ltype? unparse-Ltype unparse-Lsrc count-Lsrc
         lookup-primref primref? primref-name primref-level primref-flags primref-arity
         sorry! make-preinfo preinfo? preinfo-lambda? preinfo-sexpr preinfo-sexpr-set! preinfo-src
         make-preinfo-lambda preinfo-lambda-name preinfo-lambda-name-set! preinfo-lambda-flags preinfo-lambda-libspec
         prelex? make-prelex prelex-name prelex-name-set! prelex-flags prelex-flags-set!
         prelex-source prelex-operand prelex-operand-set! prelex-uname prelex-counter make-prelex*
         target-fixnum? target-bignum?)

  (module (lookup-primref primref? primref-name primref-flags primref-arity primref-level)
    (include "primref.ss")

    (define $lookup-primref
      (lambda (level name)
        (unless (symbol? name)
          (sorry! 'lookup-primref "invalid primitive name ~s" name))
        (or ($sgetprop name
              (case level
                [(2) '*prim2*]
                [(3) '*prim3*]
                [else ($oops 'lookup-primref "invalid level ~s" level)])
              #f)
            ($oops 'lookup-primref "unrecognized prim ~s" name))))

    (define-syntax lookup-primref
      (lambda (x)
        (define exact-integer?
          (lambda (x)
            (and (integer? x) (exact? x))))
        (define constant-level&name
          (lambda (level name)
            (unless (and (exact-integer? level) (memv level '(2 3)))
              (syntax-error x (format "invalid level ~s" level)))
            (unless (symbol? name)
              (syntax-error x (format "invalid name ~s" name)))
            (let ([primref ($sgetprop name (if (eqv? level 2) '*prim2* '*prim3*) #f)])
              (unless primref (syntax-error x (format "unknown primitive ~s" name)))
              #`'#,primref)))
        (define constant-name
          (lambda (?level name)
            (unless (symbol? name)
              (syntax-error x (format "invalid name ~s" name)))
            (let ([primref2 ($sgetprop name '*prim2* #f)]
                  [primref3 ($sgetprop name '*prim3* #f)])
              (unless (and primref2 primref3)
                (syntax-error x (format "unknown primitive ~s" name)))
              #`(let ([level #,?level])
                  (case level
                    [(2) '#,primref2]
                    [(3) '#,primref3]
                    [else (sorry! 'lookup-primref "invalid level ~s" level)])))))
        (syntax-case x (quote)
          [(_ (quote level) (quote name))
           (constant-level&name (datum level) (datum name))]
          [(_ level (quote name))
           (exact-integer? (datum level))
           (constant-level&name (datum level) (datum name))]
          [(_ ?level (quote name))
           (constant-name #'?level (datum name))]
          [(k ?level ?name) #'($lookup-primref ?level ?name)]))))
  
  (module (old-prelex? make-old-prelex
           old-prelex-name old-prelex-name-set!
           old-prelex-flags old-prelex-flags-set!
           old-prelex-source
           old-prelex-operand old-prelex-operand-set!
           old-prelex-uname)
    (define-record-type old-prelex
      (nongenerative #{prelex grpmhtzqa9bflxfggfu6pp-0})
      (sealed #t)
      (fields (mutable name) (mutable flags) source (mutable operand) (mutable $uname))
      (protocol
        (lambda (new)
          (lambda (name flags source operand)
            (new name flags source operand #f)))))
    (define old-prelex-uname
      (lambda (id)
        (or (old-prelex-$uname id)
            (let ([uname (gensym (symbol->string (old-prelex-name id)))])
              (with-tc-mutex
                (or (old-prelex-$uname id)
                    (begin (old-prelex-$uname-set! id uname) uname)))))))
    (record-writer (record-type-descriptor old-prelex)
      (lambda (x p wr)
        (fprintf p "~s" (old-prelex-name x)))))
  
  (module (new-prelex? make-new-prelex
           new-prelex-name new-prelex-name-set!
           new-prelex-flags new-prelex-flags-set!
           new-prelex-source
           new-prelex-operand new-prelex-operand-set!
           new-prelex-uname
           new-prelex-counter)
    (define-record-type new-prelex
      (nongenerative #{new-prelex my8fpg3cekjjh9zytnixui-0})
      (sealed #t)
      (fields (mutable name) (mutable flags) source (mutable operand) (mutable $uname) (mutable $counter))
      (protocol
        (lambda (new)
          (lambda (name flags source operand)
            (new name flags source operand #f #f)))))
    (define new-prelex-uname
      (lambda (id)
        (or (new-prelex-$uname id)
            (let ([uname (gensym (symbol->string (new-prelex-name id)))])
              (with-tc-mutex
                (or (new-prelex-$uname id)
                    (begin (new-prelex-$uname-set! id uname) uname)))))))
    (define counter 0)
    (define new-prelex-counter
      (lambda (id)
        (or (new-prelex-$counter id)
            (with-tc-mutex
             (or (new-prelex-$counter id)
                 (let ([c counter])
                   (set! counter (fx1+ counter))
                   (new-prelex-$counter-set! id c)
                   c))))))
    (record-writer (record-type-descriptor new-prelex)
      (lambda (x p wr)
        (fprintf p "~s" (new-prelex-name x)))))

  (module (prelex? make-prelex
           prelex-name prelex-name-set!
           prelex-flags prelex-flags-set!
           prelex-source
           prelex-operand prelex-operand-set!
           prelex-uname
           prelex-counter)
      (define (prelex? p) (or (new-prelex? p) (old-prelex? p)))
    (define make-prelex make-new-prelex)
    (define (prelex-name p) (if (new-prelex? p)
                                (new-prelex-name p)
                                (old-prelex-name p)))
    (define (prelex-name-set! p v) (if (new-prelex? p)
                                       (new-prelex-name-set! p v)
                                       (old-prelex-name-set! p v)))
    (define (prelex-flags p) (if (new-prelex? p)
                                (new-prelex-flags p)
                                (old-prelex-flags p)))
    (define (prelex-flags-set! p v) (if (new-prelex? p)
                                       (new-prelex-flags-set! p v)
                                       (old-prelex-flags-set! p v)))
    (define (prelex-source p) (if (new-prelex? p)
                                  (new-prelex-source p)
                                  (old-prelex-source p)))
    (define (prelex-operand p) (if (new-prelex? p)
                                (new-prelex-operand p)
                                (old-prelex-operand p)))
    (define (prelex-operand-set! p v) (if (new-prelex? p)
                                       (new-prelex-operand-set! p v)
                                       (old-prelex-operand-set! p v)))
    (define (prelex-uname p) (if (new-prelex? p)
                                 (new-prelex-uname p)
                                 (old-prelex-uname p)))
    (define (prelex-counter p) (if (new-prelex? p)
                                   (new-prelex-counter p)
                                   (symbol-hash (old-prelex-uname p)))))

  #;
  (module (prelex? make-prelex
           prelex-name prelex-name-set!
           prelex-flags prelex-flags-set!
           prelex-source
           prelex-operand prelex-operand-set!
           prelex-uname
           prelex-counter)
    (define-record-type prelex
      (nongenerative #{prelex my8fpg3cekjjh9zytnixui-0})
      (sealed #t)
      (fields (mutable name) (mutable flags) source (mutable operand) (mutable $uname) (mutable $counter))
      (protocol
        (lambda (new)
          (lambda (name flags source operand)
            (new name flags source operand #f #f)))))
    (define prelex-uname
      (lambda (id)
        (or (prelex-$uname id)
            (let ([uname (gensym (symbol->string (prelex-name id)))])
              (with-tc-mutex
                (or (prelex-$uname id)
                    (begin (prelex-$uname-set! id uname) uname)))))))
    (define counter 0)
    (define prelex-counter
      (lambda (id)
        (or (prelex-$counter id)
            (with-tc-mutex
             (or (prelex-$counter id)
                 (let ([c counter])
                   (set! counter (fx1+ counter))
                   (prelex-$counter-set! id c)
                   c))))))
    (record-writer (record-type-descriptor prelex)
      (lambda (x p wr)
        (fprintf p "~s" (prelex-name x)))))

  (define make-prelex*
    (case-lambda
      [() (make-prelex (gensym) 0 #f #f)]
      [(name) (make-prelex name 0 #f #f)]))

  ; TODO: use sorry! where appropriate
  (define sorry!
    (lambda (who str . arg*)
      ($oops 'compiler-internal "~@[~a: ~]~?" who str arg*)))

  (define maybe-source-object?
    (lambda (x)
      (or (eq? x #f) (source-object? x))))

  (define rcd?
    (lambda (x)
      (or (record-constructor-descriptor? x) #t))) ; rcd should be retricted to rcd or ctrcd

  (define exact-integer?
    (lambda (x)
      (and (integer? x) (exact? x))))

  (meta-cond
    [(= (constant fixnum-bits) (fixnum-width))
     (define target-fixnum? fixnum?)
     (define target-bignum? bignum?)]
    [(< (constant fixnum-bits) (fixnum-width))
     (define target-fixnum?
       (lambda (x)
         (and (fixnum? x)
              (fx<= (constant most-negative-fixnum) x (constant most-positive-fixnum)))))
     (define target-bignum?
       (lambda (x)
         (or (bignum? x)
             (and (fixnum? x)
                  (not (fx<= (constant most-negative-fixnum) x (constant most-positive-fixnum)))))))]
    [else
     (define target-fixnum?
       (lambda (x)
         (or (fixnum? x)
             (and (bignum? x)
                  (<= (constant most-negative-fixnum) x (constant most-positive-fixnum))))))
     (define target-bignum?
       (lambda (x)
         (and (bignum? x)
              (not (<= (constant most-negative-fixnum) x (constant most-positive-fixnum))))))])

  (define $prelex?
    (lambda (x)
      (prelex? x)))

  (define datum?
    (lambda (x)
      #t))

  (define convention?
    (lambda (x)
      (or (eq? x #f) (symbol? x))))

  (define-record-type preinfo
    (nongenerative #{preinfo e23pkvo5btgapnzomqgegm-2})
    (fields src (mutable sexpr))
    (protocol
      (lambda (new)
        (case-lambda
          [() (new #f #f)]
          [(src) (new src #f)]
          [(src sexpr) (new src sexpr)]))))

  (define-record-type preinfo-lambda
    (nongenerative #{preinfo-lambda e23pkvo5btgapnzomqgegm-4})
    (parent preinfo)
    (sealed #t)
    (fields libspec (mutable name) flags)
    (protocol
      (lambda (pargs->new)
        (case-lambda
          [() ((pargs->new) #f #f 0)]
          [(src) ((pargs->new src) #f #f 0)]
          [(src sexpr) ((pargs->new src sexpr) #f #f 0)]
          [(src sexpr libspec) ((pargs->new src sexpr) libspec #f 0)]
          [(src sexpr libspec name) ((pargs->new src sexpr) libspec name 0)]
          [(src sexpr libspec name flags) ((pargs->new src sexpr) libspec name flags)]))))

  ; language of foreign types
  (define-language Ltype 
    (nongenerative-id #{Ltype czp82kxwe75y4e18-0})
    (terminals
      (exact-integer (bits))
      ($ftd (ftd)))
    (Type (t)
      (fp-integer bits)
      (fp-unsigned bits)
      (fp-void)
      (fp-scheme-object)
      (fp-u8*)
      (fp-u16*)
      (fp-u32*)
      (fp-fixnum)
      (fp-double-float)
      (fp-single-float)
      (fp-ftd ftd)))

  (define arity?
    (lambda (x)
      (or (eq? x #f)
          (for-all fixnum? x))))

  (define maybe-string? (lambda (x) (or (eq? x #f) (string? x))))

  ; source language used by the passes leading up to the compiler or interpreter
  (define-language Lsrc
    (nongenerative-id #{Lsrc czsa1fcfzdeh493n-2})
    (terminals
      (preinfo (preinfo))
      ($prelex (x))
      (datum (d))
      (record-type-descriptor (rtd))
      (rcd (rcd))
      (source-object (src))
      (maybe-source-object (maybe-src))
      (Ltype (arg-type result-type))        => unparse-Ltype
      (fixnum (interface index flags level))
      (arity (arity))
      (box (box))
      (convention (conv))
      (maybe-string (name))
      (symbol (sym type))
      (primref (pr)))
    (Expr (e body rtd-expr)
      pr
      (moi)
      (ref maybe-src x)                                     => x
      (quote d)
      (if e0 e1 e2)
      (seq e0 e1)
      (set! maybe-src x e)                                  => (set! x e)
      (pariah)
      (case-lambda preinfo cl ...)                          => (case-lambda cl ...)
      (letrec ([x* e*] ...) body)
      (letrec* ([x* e*] ...) body)
      (call preinfo e0 e1 ...)                              => (e0 e1 ...)
      (record-type rtd e)
      (record-cd rcd rtd-expr e)
      (immutable-list (e* ...) e)
      (record rtd rtd-expr e* ...)
      (record-ref rtd type index e)
      (record-set! rtd type index e1 e2)
      (cte-optimization-loc box e)
      (foreign conv name e (arg-type* ...) result-type)
      (fcallable conv e (arg-type* ...) result-type)
      (profile src)                                         => (profile)
      ; used only in cpvalid
      (cpvalid-defer e))
    (CaseLambdaClause (cl)
      (clause (x* ...) interface body)                      => [(x* ...) interface body]))

  (define-language-node-counter count-Lsrc Lsrc)
  )
