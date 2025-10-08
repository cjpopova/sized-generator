#lang racket

(define file
  (command-line
   #:args (filename) ; expect one command-line argument: <filename>
   filename))

(define i -1)
(define (cat/stream f)
  (call-with-input-file f
    (λ (p)
      (define strm (sequence->stream (in-lines p)))
      ; initialize vectors with the number of tests
      (define s (stream-first strm))
      (define mtch (regexp-match #px"num tests: (\\d+)" s))
      (unless mtch 
        (error 'cat/stream "Failed to read number of tests from first line: ~a" s))
      (define num-test (string->number (second mtch)))
      (define num-funcs (make-vector num-test 0))
      (define max-calls (make-vector num-test 0))
      
      ; loop over the rest of stream to update vectors
      (let loop ([s (stream-rest strm)])
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
      (loop (stream-rest s))))
    (displayln num-funcs)
    (displayln max-calls))))

(cat/stream file)