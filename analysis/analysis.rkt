#lang racket

(define num-funcs (make-vector 1000 0))
(define max-calls (make-vector 1000 0))

(define i -1)
(define (cat/stream f)
  (call-with-input-file f
    (λ (p)
      (let loop ([s (sequence->stream (in-lines p))])
        (unless (stream-empty? s)
          (define str (stream-first s))
          (cond
            [(equal? str "") (void)]
            [(string-prefix? str "test") (set! i (add1 i))]
            [(string-prefix? str "#<procedure")
             (let ([mtch (regexp-match #px"#<procedure:.*> (\\d+)" str)])
               (when mtch
                 (define cnt (string->number (second mtch)))
                 (vector-set! num-funcs i (add1 (vector-ref num-funcs i)))
                 (vector-set! max-calls i (max (vector-ref max-calls i) cnt))))])

#;(displayln (stream-first s))
(loop (stream-rest s)))))))

(cat/stream "thousand1.txt")

(displayln num-funcs)
(displayln max-calls)