(define sexpr->ocaml-pattern
(lambda (e)
(cond
((boolean? e)
(if e "Bool true" "Bool false"))
((null? e) "Nil")
((char? e) (format "Char '~a'" e))
((symbol? e) (format "Symbol \"~a\"" e))
((string? e) (format "String \"~a\"" e))
((integer? e) (format "Number (Int ~a)" e))
((rational? e) (format "Number (Float ~a)" e))
((pair? e) (format "Pair(~a, ~a)"
(sexpr->ocaml-pattern (car e))
(sexpr->ocaml-pattern (cdr e))))
((vector? e)
(format "Vector [~a]"
(fold-right (lambda (v lst) `(,v ";" ,@lst)) '()
(map sexpr->ocaml-pattern (vector->list e)))))
(else (error 'sexpr->ocaml-pattern
(format "Unsupported type: ~a" e))))))


(display (sexpr->ocaml-pattern 
    '(EXPR => EXPRf)
))