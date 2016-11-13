#lang racket

; === Parser and Interpreter *SKELETON* 
;           for the language given in Exercise 4, CIS505/705, 
;        Kansas State University, Fall 2016.
;    Torben Amtoft

; --- what is visible to the outside

(provide run-parser)
(provide run)

; --- syntax

;  op ::= +
;      |  -
;      |  *
;
; exp ::= id
;      |  num
;      |  "lambda" id exp0
;      |  "apply" exp1 "to" exp2 
;      |  "if" exp0 "{" exp1 "}" "{" exp2 "}"
;      |  "let" id "{" exp1 "}" exp0
;      |  "letclass" id "{" id1 .. idn "}" exp0
;      |  "(" exp1 op exp2 ")"
;      |  "("exp1 ";" exp2 ")"
;      |  "new" id
;      |  "get" exp1 "." id
;      |  "set" exp1 "." id "to" exp2

; === lexical analysis
; ----env- ---|-----sto-------
; id ------> loc --------> value

; --- tokens

(struct IdentT (string))
(struct NumT (num))
(struct OpenParenT ())
(struct CloseParenT ())
(struct OpenCurlyT ())
(struct CloseCurlyT ())
(struct PlusT ())
(struct MinusT ())
(struct TimesT ())
(struct LambdaT ())
(struct ApplyT ())
(struct ToT ())
(struct IfT ())
(struct LetT ())
(struct LetClassT ())
(struct NewT ())
(struct GetT ())
(struct SetT ())
(struct SemiT ())
(struct DotT ())

(define (char->digit ch)
  (- (char->integer ch) (char->integer #\0)))
  
(define (lexer chars)
   (if (null? chars)
      null
      (let ([current (first chars)] [remain (rest chars)])
         (cond
           [(eq? current #\() (cons (OpenParenT) (lexer remain))]
           [(eq? current #\)) (cons (CloseParenT) (lexer remain))]
           [(eq? current #\{) (cons (OpenCurlyT) (lexer remain))]
           [(eq? current #\}) (cons (CloseCurlyT) (lexer remain))]
	   [(eq? current #\+) (cons (PlusT) (lexer remain))]
	   [(eq? current #\-) (cons (MinusT) (lexer remain))]
           [(eq? current #\*) (cons (TimesT) (lexer remain))]
	   [(eq? current #\;) (cons (SemiT) (lexer remain))]
	   [(eq? current #\.) (cons (DotT) (lexer remain))]
           [(eq? current #\space) (lexer remain)]
	   [(eq? current #\newline) (lexer remain)]	   	   
	   [(char-numeric? current) (num-state (char->digit current) remain)]
	   [(char-alphabetic? current) (ident-state (list current) remain)]
	   [else (display (string-append "unknown symbol "
	                         (list->string (list current)) "\n"))]
	))))

(define (num-state seen chars)
   (if (and (pair? chars) (char-numeric? (first chars)))
      (num-state (+ (* 10 seen) (char->digit (first chars))) (rest chars))
      (cons (NumT seen) (lexer chars))
    ))

(define (ident-state seen chars)
   (if (and (pair? chars) 
          (or (char-alphabetic? (first chars))
              (char-numeric? (first chars))))
      (ident-state (append seen (list (first chars))) (rest chars))
      (cons (mk-alpha-token (list->string seen)) (lexer chars))
   ))

(define (mk-alpha-token seen)
   (cond
      [(equal? seen "lambda") (LambdaT)]
      [(equal? seen "apply") (ApplyT)]
      [(equal? seen "to") (ToT)]      
      [(equal? seen "if") (IfT)]
      [(equal? seen "let") (LetT)]      
      [(equal? seen "letclass") (LetClassT)]      
      [(equal? seen "new") (NewT)]      
      [(equal? seen "get") (GetT)]      
      [(equal? seen "set") (SetT)]      
      [else (IdentT seen)]
     ))

(define (run-lexer x) (lexer (string->list x)))

; === parsing

; --- syntax trees

(struct IdentExp (id))
(struct NumExp (num))
(struct LambdaExp (formal body))
(struct ApplyExp (fun arg))
(struct IfExp (test exp1 exp2))
(struct LetExp (id exp1 body))
(struct LetClassExp (class ids body))
(struct PlusExp (exp1 exp2))
(struct MinusExp (exp1 exp2))
(struct TimesExp (exp1 exp2))
(struct SeqExp (exp1 exp2))
(struct NewExp (class))
(struct GetExp (obj id))
(struct SetExp (obj id exp2))

(define (parExpectIdent error-msg tks)
   (if (and (pair? tks) (IdentT? (first tks)))
      (values (IdentT-string (first tks)) (rest tks))
      (display error-msg)
   ))

(define (parGetIdentList tks)
   (if (and (pair? tks) (IdentT? (first tks)))
      (let-values ([(ids tks1) (parGetIdentList (rest tks))])
         (values (cons (IdentT-string (first tks)) ids) tks1))
      (values null tks)
   ))

(define (parExpect what? error-msg tks)
   (if (and (pair? tks) (what? (first tks)))
      (values "dummy" (rest tks))
      (display error-msg)
   ))

(define (parExp tks)
   (if (pair? tks)
      (let ([tk (first tks)] [tks0 (rest tks)])
         (cond
            [(IdentT? tk)
               (values (IdentExp (IdentT-string tk)) tks0)]
            [(NumT? tk)
               (values (NumExp (NumT-num tk)) tks0)]
 	    [(LambdaT? tk)
 	       (let*-values (
 	          [(id tks1) (parExpectIdent
 		                 "identifier expected after 'lambda'\n" tks0)]
		  [(e tks2) (parExp tks1)])
   		 (values (LambdaExp id e) tks2))]
 	    [(ApplyT? tk)
 	       (let*-values (
 	          [(e1 tks1) (parExp tks0)]
                  [(_  tks2) (parExpect ToT? "'to' expected in 'apply'\n" tks1)]
 		  [(e2 tks3) (parExp tks2)])
 		 (values (ApplyExp e1 e2) tks3))]
	    [(IfT? tk)
	       (let*-values (
	          [(e0 tks1) (parExp tks0)]
                  [(_  tks2) (parExpect OpenCurlyT? "'{' expected\n" tks1)]
		  [(e1 tks3) (parExp tks2)]
                  [(_  tks4) (parExpect CloseCurlyT? "'}' expected\n" tks3)]
                  [(_  tks5) (parExpect OpenCurlyT? "'{' expected\n" tks4)]
		  [(e2 tks6) (parExp tks5)]
                  [(_  tks7) (parExpect CloseCurlyT? "'}' expected\n" tks6)])
		 (values (IfExp e0 e1 e2) tks7))]
 	    [(LetT? tk)
 	       (let*-values (
 	          [(id tks1) (parExpectIdent
 		                 "identifier expected after 'let'\n" tks0)]
                  [(_  tks2) (parExpect OpenCurlyT? 
                                 (string-append "'{' expected after 'let "
                                    id "'\n") tks1)]
		  [(e1 tks3) (parExp tks2)]
                  [(_  tks4) (parExpect CloseCurlyT? 
                      "'}' expected in 'let'\n" tks3)]
		  [(e0 tks5) (parExp tks4)])
   		 (values (LetExp id e1 e0) tks5))]
 	    [(LetClassT? tk)
 	       (let*-values (
 	          [(class tks1) (parExpectIdent
 		                 "identifier expected after 'letclass'\n" tks0)]
                  [(_  tks2) (parExpect OpenCurlyT? 
                                 (string-append "'{' expected after 'letclass "
                                     class "'\n") tks1)]
		  [(ids tks3) (parGetIdentList tks2)]
                  [(_  tks4) (parExpect CloseCurlyT? 
                      "'}' expected in 'letclass'\n" tks3)]
		  [(e0 tks5) (parExp tks4)])
   		 (values (LetClassExp class ids e0) tks5))]
 	    [(NewT? tk)
 	       (let-values (
 		  [(class tks1) (parExpectIdent 
                                   "identifier expected after 'new'\n"
                                   tks0)])
                 (values (NewExp class) tks1))]
 	    [(GetT? tk)
 	       (let*-values (
 	          [(obj tks1) (parExp tks0)]
                  [(_  tks2) (parExpect DotT? "'.' expected in 'get'\n" tks1)]
		  [(id tks3) (parExpectIdent 
                                "identifier expected after '.'\n" 
                                tks2)])
   		 (values (GetExp obj id) tks3))]
 	    [(SetT? tk)
 	       (let*-values (
 	          [(obj tks1) (parExp tks0)]
                  [(_  tks2) (parExpect DotT? "'.' expected in 'set'\n" tks1)]
		  [(id tks3) (parExpectIdent 
                                 "identifier expected after '.'\n" tks2)]
                  [(_  tks4) (parExpect ToT? "'to' expected in 'set'\n" tks3)]
 		  [(e2 tks5) (parExp tks4)])
   		 (values (SetExp obj id e2) tks5))]
            [(OpenParenT? tk)
              (let*-values (
	          [(e1 tks1) (parExp tks0)]
	          [(op tks2) 
                      (if (pair? tks1) 
                         (values (first tks1) (rest tks1))
                         (display "'+,'-','*' or ';' expected after '('\n"))]
		  [(e2 tks3) (parExp tks2)]
		  [(_ tks4)  (parExpect CloseParenT?
		                "closing parenthesis expected\n"
				tks3)])
                (let ([exp (cond [(SemiT? op) (SeqExp e1 e2)]
                              [(PlusT? op) (PlusExp e1 e2)]
                              [(MinusT? op) (MinusExp e1 e2)]
                              [(TimesT? op) (TimesExp e1 e2)]
                              [else (display "'+','-','*' or ';' expected after '('\n")])])
                  (values exp tks4)))]
            [else (display "not proper start of expression\n")]
          ))
      (display "expression expected\n")
   ))
   
(define (parse tks)
   (let-values ([(main tks1) (parExp tks)])
      (if (null? tks1)
         main
	 (display "program read but more input given\n"))
    ))

(define (run-parser x) (parse (run-lexer x)))

; === evaluating (abstract) syntax

; --- Locations
;   represented as integers

(define locs (box 0))

(define (new-loc!)
   (let ([_ (set-box! locs (+ 1 (unbox locs)))])
       (unbox locs)))

; --- denotable values
;    either locations, or (for a class definition) sets of field names

(struct Location (loc))
(struct ClassDef (fields))

; --- environments
;   * binds identifiers to denotable values
;   * are represented as a list of pairs

(define (extend-env id dval env)
  (cons (cons id dval) env)
 )

(define (lookup-env error-msg id env)
  (cond
     [(null? env)
        (display (string-append error-msg " " id "\n"))]
     [(equal? id (car (first env)) )
        (cdr (first env))]
     [else (lookup-env error-msg id (rest env))]
  ))

; binds the identifiers in 'ids' to fresh locations
(define (new-env! ids)
   (if (null? ids)
      null
      (cons
         (cons
            (first ids)
            (Location (new-loc!)))
         (new-env! (rest ids)))
   ))

; --- stores
;   * binds locations to values
;   * represented as a list of pairs

(define (extend-sto loc val sto)
  (cons (cons loc val) sto)
 )

(define (lookup-sto loc sto)
  (cond
     [(null? sto)
        (display "undefined memory location\n")]
     [(equal? loc (car (first sto)) )
        (cdr (first sto))]
     [else (lookup-sto loc (rest sto))]
  ))

; --- values

(struct NumVal (num))
(struct ClosureVal (formal body env))
(struct Object (env))  
   ; this environment maps all identifiers to locations

(define (interp exp env sto)
   (cond
      [(IdentExp? exp)
          (let ([dval (lookup-env "undeclared identifier"
                                  (IdentExp-id exp) env)])
            (if (Location? dval)
                   (values  (lookup-sto dval sto) sto)  ;;; CHANGED!! (lookup location in store)
                   (display "class name occurs outside 'new'\n")))]
      [(NumExp? exp) (values (NumVal (NumExp-num exp)) sto)]
      [(LambdaExp? exp)
            (values (ClosureVal (LambdaExp-formal exp) (LambdaExp-body exp) env) sto)]  ;;; CHANGED!
      [(ApplyExp? exp)
          (let*-values 
               ([(v1 sto1) (interp (ApplyExp-fun exp) env sto)]
	             [(v2 sto2) (interp (ApplyExp-arg exp) env sto1)]
                [(loc) (Location new-loc!)]
                [(sto3) (extend-sto loc v2 sto2)]
                [(env2) (extend-env (ClosureVal-formal v1) loc (ClosureVal-env v1))]
               )
             (interp (ClosureVal-body v1) env2 sto3)
                  ;;; CHANGE, as on last slide of 'InterpretMutations'
         )]
      [(IfExp? exp)
          (let-values 
               ([(v0 sto0) (interp (IfExp-test exp) env sto)])
           (if (and (NumVal? v0) (> (NumVal-num v0) 0))
             (interp (IfExp-exp1 exp) env sto0)   ;;; CHANGED
             (interp (IfExp-exp2 exp) env sto0)   ;;; CHANGED
           ))]
      [(LetExp? exp)
          (let*-values
              (
               [(v1 sto1) (interp (LetExp-exp1 exp) env sto)]
               [(loc) (Location (new-loc!))]
               [(sto2) (extend-sto loc v1 sto1)]
               [(env2) (extend-env (LetExp-id exp) loc env)]
              )
            (interp (LetExp-body exp) env2 sto2))
              ;;; CHANGE using last remark on last slide of 'InterpretMutations'
      ]
      [(LetClassExp? exp)
       (let*-values
        (
         [(loc) (Location (new-loc!))]
         [(env1) (extend-env (LetClassExp-class exp) loc env)]
         [(env2) (new-env! (LetClassExp-ids exp))]
        )
       (interp
              (LetClassExp-body exp)
              env1 ;;; CHANGE
              (extend-sto loc env2 sto)))]
      [(PlusExp? exp)
         (let*-values ([(a1 st1) (interp (PlusExp-exp1 exp) env sto)]
                       [(a2 st2) (interp (PlusExp-exp2 exp) env st1)])
           (values (NumVal (+ (NumVal-num a1) (NumVal-num a2))) st2))] ;;;Changed
      [(MinusExp? exp)
         (let*-values ([(a1 st1) (interp (MinusExp-exp1 exp) env sto)]
                       [(a2 st2) (interp (MinusExp-exp2 exp) env st1)])
           (values (NumVal (- (NumVal-num a1) (NumVal-num a2))) st2))]  ;;; CHANGED
      [(TimesExp? exp)
         (let*-values ([(a1 st1) (interp (TimesExp-exp1 exp) env sto)]
                       [(a2 st2) (interp (TimesExp-exp2 exp) env st1)])
           (values (NumVal (* (NumVal-num a1) (NumVal-num a2))) st2))]  ;;; CHANGED
      [(SeqExp? exp)
       (let*-values
           ([(v0 sto0) (interp (SeqExp-exp1 exp) env sto)])
         (interp (SeqExp-exp2 exp) env sto0))];;; CHANGED
      [(NewExp? exp)
          (let*-values (
                        [(dval) (lookup-env "undeclared identifier" (NewExp-class exp) env)]
                        [(loc) (Location (new-loc!))]
                       )
             (values (Object (lookup-sto dval sto)) (extend-sto loc ) ;;; CHANGE
        )]
      [(GetExp? exp)
          (let*-values 
               ([(v0 sto0) (interp (GetExp-obj exp) env sto)]
                [(loc) (lookup-env "" (GetExp-id exp) (Object-env v0))])
             (values (lookup-sto loc sto0) sto0) ;;; CHANGE
         )]
      [(SetExp? exp)
          (let*-values 
               ([(v0 sto0) (interp (SetExp-obj exp) env sto)]
                [(v2 sto1) (interp (SetExp-exp2 exp) env sto0)]
                [(loc) (lookup-env "" (SetExp-id exp) (Object-env v0))]
                [(newsto) (extend-sto loc v2 sto1)] 
               )
             (values null newsto) ;;; CHANGE
          )]
  ))

(define (run x)
   (let ([main (run-parser x)])
     (let-values ([(v sto) (interp main null null)])
       (cond
         [(NumVal? v) (NumVal-num v)]
	 [else (display "program must return a number\n")]
    ))))

