(ns lambdafuck.core
  (:require [clojure.tools.logging :refer [error]])
  (:refer-clojure :exclude [inc zero? delay dec read and]))

(defmacro af [f & args]
  (if (seq args)
    `(af (~f ~(first args)) ~@(rest args))
    f))

(defmacro fun [args body]
  (if (seq args)
    `(fn [~(first args)] (fun ~(rest args) ~body))
    body))

(defmacro catch-errors [& body]
  `(try
     ~@body
     (catch Exception e#
       (error e# "wat")
       (throw e#))))

(def truth
  (fun [t f] t))

(def falsehood
  (fun [t f] f))

(defmacro delay [v]
  `(fn [x#]
     (~v x#)))

(def and
  (fun [b1 b2]
    (af b1 b2 falsehood)))

(def pair
  (fun [a b]
    (fun [selector nil-val]
      (af selector a b))))

(def null
  (fun [selector nil-val]
    nil-val))

(def null?
  (fn [p]
    (af p
        (fun [a b] falsehood)
        truth)))

(defmacro iff [b t f]
  `((af
     ~b
     (fn [_#] ~t)
     (fn [_#] ~f))
    null))

(defn to-bool [b] (af b true false))

(defn from-seq [s]
  (fun [selector nil-val]
    (if (seq s)
      (af selector (first s) (from-seq (rest s)))
      nil-val)))

(def car
  (fn [p]
    (af p
        (fun [f r] f)
        null)))

(def cdr
  (fn [p]
    (af p
        (fun [f r] r)
        null)))

(defn to-seq [p]
  (lazy-seq
    (af p
        (fun [f r]
          (cons f (to-seq r)))
        nil)))


(to-seq (from-seq (range 5)))

(defn spyseq [s]
  (lazy-seq
    (when (seq s)
      (println (first s))
      (cons (first s) (spyseq (rest s))))))

(def s (to-seq (from-seq (spyseq (range 20)))))

(def s (-> 20
           range
           spyseq
           from-seq
           to-seq
           from-seq
           to-seq))

(take 3 s)

;;; New numbers

(defn Y [f]
  ((fn [x] (x x))
   (fn [x]
     (f (fn [y]
          ((x x) y))))))

(defmacro defrec [name body]
  `(def ~name
     (Y
      (fn [~name]
        ~body))))

(defmacro if-seq [s fst rst body ncase]
  `(af ~s (fun [~fst ~rst] ~body) ~ncase))

(defmacro when-seq [s fst rst body]
  `(if-seq ~s ~fst ~rst ~body null))

(def zero null)

(def inc
  (fn [n]
    (af pair null n)))

(def zero? null?)

(def dec cdr)

(defrec an*
  (fun [n f]
    (fn [x]
      (iff (null? n)
        x
        (f ((af an* (dec n) f) x))))))

(defmacro an [n f]
  `(af an* ~n ~f))

(defrec equals
  (fun [n1 n2]
    (iff (null? n1)
      (null? n2)
      (iff (null? n2)
        falsehood
        (af equals (dec n1) (dec n2))))))

;;; End new numbers

(defn to-num [n]
  ((an n clojure.core/inc) 0))

(defrec add
  (fun [a b]
    (iff (zero? a)
      b
      (af add (dec a) (inc b)))))

(def tape
  (fun [ls v rs]
    (fn [reader]
      (af reader ls v rs))))

(def read-tape
  (fn [t]
    (t (fun [_ v _] v))))

(def apply-tape
  (fun [f t]
    (t (fun [ls v rs]
         (af tape ls (f v) rs)))))

(def write-tape
  (fun [t v]
    (af apply-tape (fn [_] v) t)))

(def left-tape
  (fn [t]
    (t (fun [ls v rs]
         (when-seq ls
           fst rst
           (af tape rst fst (af pair v rs)))))))

(def right-tape
  (fn [t]
    (t (fun [ls v rs]
         (when-seq rs
           fst rst
           (af tape (af pair v ls) fst rst))))))

(defrec repeat-forever
  (fn [x]
    (af pair x (delay (repeat-forever x)))))

(def inc-tape (apply-tape inc))

(def dec-tape (apply-tape dec))

(def blank-tape (af tape (repeat-forever zero) zero (repeat-forever zero)))

(-> blank-tape
    inc-tape
    left-tape
    inc-tape
    left-tape
    read-tape
    to-num)

(defmacro defenum [& elements]
  `(do
     ~@(for [e elements]
         `(do
            (def ~e (fun [~@elements] ~e))
            (def ~(symbol (str (name e) \?)) (fn [t#] (af t# ~@(for [e2 elements] (if (= e e2) `truth `falsehood)))))))))

(defenum lshift rshift plus minus lbrace rbrace read write)

(defmacro lett [bind body]
  (if (seq bind)
    `((fn [~(first bind)]
        (lett ~(drop 2 bind) ~body))
      ~(second bind))
    body))

(defmacro deftuple [tname & elements]
  `(do
     (def ~tname
       (fun [~@elements]
         (fn [reader#]
           (af reader# ~@elements))))
     ~@(for [e elements]
         `(do
            (def ~(symbol (str "get-" (name e)))
              (fn [t#]
                (t# (fun [~@elements] ~e))))
            (def ~(symbol (str "alter-" (name e)))
              ~(let [f (gensym)
                     t (gensym)
                     new-val (gensym)]
                 `(fun [~f ~t]
                    (lett [~new-val  (~f (~(symbol (str "get-" (name e))) ~t))]
                       (~t
                         (fun [~@elements]
                           (af ~tname ~@(for [e2 elements] (if (= e2 e) new-val e2)))))))))))))

(deftuple brainfuck-state jump-table instructions tape inputs instruction-counter)

(deftuple parse-state parse-instructions loop-stack pairs parse-counter)

(def parse-stepper
  (fn [state]
    (->>
      (iff (lbrace? (car (get-parse-instructions state)))
        (af alter-loop-stack (pair (get-parse-counter state)) state)
        (iff (rbrace? (car (get-parse-instructions state)))
          (lett [popped-counter (car (get-loop-stack state))]
            (->> state
                 (af alter-loop-stack cdr)
                 (af alter-pairs (pair (af pair (get-parse-counter state) popped-counter))))) state))
      (af alter-parse-instructions cdr)
      (af alter-parse-counter inc))))

(defrec do-parse-state
  (fn [state]
    (iff (null? (get-parse-instructions state))
      (get-pairs state)
      (do-parse-state
        (parse-stepper
          state)))))

(defn parse-brainfuck-string [s]
  (from-seq
    (filter identity (map {\[ lbrace
                           \] rbrace
                           \+ plus
                           \- minus
                           \, read
                           \. write
                           \< lshift
                           \> rshift} s))))


(comment
  (map
    (fn [p] [(to-num (car p)) (to-num (cdr p))])
    (to-seq (do-parse-state (af parse-state (parse-brainfuck-string "[[+-,.]hello world[[]]]") null null zero)))))

(defrec mapp
  (fun [f s]
    (when-seq s
      fst rst
      (af pair (f fst) (af mapp f rst)))))

(def run-one
  (fn [state]
;    (println "running instruction" (to-num (get-instruction-counter state)))
    (catch-errors
      (when-seq (get-instructions state)
        ins _
        (when-seq (ins state)
          pfun new-state
          (af pair
            pfun
            (->>
              new-state
              (af alter-instructions cdr)
              (af alter-instruction-counter inc))))))))

(defrec run-brainfuck-state
  (fn [state]
    (catch-errors
      (when-seq (run-one state)
        print-output new-state
        (print-output
          (delay
            (run-brainfuck-state new-state)))))))

(def id (fn [x] x))

(def no-print
  (fn [state]
    (af pair id state)))

(def tape-action
  (fn [tapefn]
    (fn [state]
      (no-print (af alter-tape tapefn state)))))

(def do-lshift (tape-action left-tape))
(def do-rshift (tape-action right-tape))
(def do-plus (tape-action inc-tape))
(def do-minus (tape-action dec-tape))

(def do-write
  (fn [state]
    (lett [v (read-tape (get-tape state))]
      (do
        #_(println "writing" (to-num v))
        (af pair (fn [s] (af pair v s)) state)))))

(def do-read
  (fn [state]
    (lett [v (car (get-inputs state))]
      (no-print
        (->> state
          (af alter-inputs cdr)
          (af alter-tape (fn [tape]
                           (af write-tape tape v))))))))

(defn dump-jump-table [jump-table]
  (doseq [[i e] (map vector (range) (to-seq jump-table))]
    (println "at " i (when (not (to-bool (null? e)))
                       (str " jump to " (to-num (car e)))))))

(def get-nth
  (fun [n s]
    (car ((an n cdr) s))))

(defn from-num [n]
  (if (= n 0)
    zero
    (inc (from-num (- n 1)))))

(af get-nth (from-num 5) (from-seq (range 20)))

(def do-jump
  (fn [state]
    (lett [counter (get-instruction-counter state)
           jump-table (get-jump-table state)
           jump-to (af get-nth counter jump-table)]
      (->> state
           (af alter-instructions (fn [_] (cdr jump-to)))
           (af alter-instruction-counter (fn [_] (car jump-to)))))))

(defn dump-instructions [state]
  (println (to-seq (get-instructions state))))

(def do-lbrace
  (fn [state]
    (no-print
      (iff (zero? (read-tape (get-tape state)))
        (do-jump state)
        state))))

(def do-rbrace
  (fn [state]
    (no-print
      (iff (zero? (read-tape (get-tape state)))
        state
        (do-jump state)))))

(def assemble-instructions
  (mapp
    (fn [i]
      (af i
          do-lshift
          do-rshift
          do-plus
          do-minus
          do-lbrace
          do-rbrace
          do-read
          do-write))))

(defrec look-in-pairs
  (fun [n pairs]
    (when-seq pairs
      fpair rpairs
      (when-seq fpair
        na nb
        (iff (af equals n na)
          (af pair nb null)
          (iff (af equals n nb)
            (af pair na null)
            (af look-in-pairs n rpairs)))))))

(defrec make-jump-table
  (fun [pairs instructions remaining-instructions counter]
    (when-seq remaining-instructions
      _ _
      (af
        pair
        (do
          (println "looking up" (to-num counter))
          (when-seq (af look-in-pairs counter pairs)
            jump-to _
            (do
              (println "jump from " (to-num counter) " to " (to-num jump-to))
              (af
                pair
                jump-to
                ((an jump-to cdr) instructions)))))
        (af make-jump-table pairs instructions (cdr remaining-instructions) (inc counter))))))

(defn print-pairs [pairs]
  (doseq [p (to-seq pairs)]
    (println (str (to-num (car p)) " " (to-num (cdr p))))))

(def construct-state
  (fun [instructions inputs]
    (lett [assembled (assemble-instructions instructions)
           pairs (do-parse-state (af parse-state instructions null null zero))
           jump-table (af make-jump-table pairs assembled assembled zero)]
      (af brainfuck-state jump-table assembled blank-tape inputs zero))))

(def run-brainfuck
  (fun [instructions inputs]
    (run-brainfuck-state (af construct-state instructions inputs))))

#_(defn get-input
  ([]
   (let [scr (lanterna.screen/get-screen)]
     (lanterna.screen/start scr)
     (get-input scr)))
  ([scr]
   (lazy-seq
     (cons (lanterna.screen/get-key-blocking scr) (get-input scr)))))

(defn lmap [f s]
  (lazy-seq
    (catch-errors
      (when (seq s)
        (cons (f (first s)) (lmap f (rest s)))))))

(defn drive-brainfuck [progstring input]
  (let [instructions (parse-brainfuck-string progstring)
        encoded-input (from-seq (lmap #(from-num (long %)) input))
        encoded-output (af run-brainfuck instructions encoded-input)]
    (lmap #(char (to-num %)) (to-seq encoded-output))))

(defn print-brainfuck [progstring input]
  (doseq [c (drive-brainfuck progstring input)]
    (print c)
    (flush)))

(comment
  (require 'lanterna.screen)

  (let [instructions  (parse-brainfuck-string
                        "++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.+++++++..+++.>++.<<+++++++++++++++.>.+++.------.--------.>+.>.")
        start-state (af construct-state instructions null)
        jump-table (get-jump-table start-state)]
    (null?
      (af get-nth (from-num 41) jump-table))

    )

  (def scr (lanterna.screen/get-screen))

  (lanterna.screen/start scr)

  (lanterna.screen/get-key-blocking scr)

  (def p (slurp "/Users/michael.blume/workspace/BrainFuck.hs/PRIME.BF"))

  (def p2 (filter (into #{} "{}<>.,+-") p))
  (count p2)

  (long \a))
