(ns lambdafuck.core
  (:require [clojure.tools.logging :refer [error]])
  (:refer-clojure :exclude [inc zero? delay dec read and]))

;; Nice Macros

(defmacro lett [bind body]
  (if (seq bind)
    `((fn [~(first bind)]
        (lett ~(drop 2 bind) ~body))
      ~(second bind))
    body))

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

(defmacro delay [v]
  `(fn [x#]
     (~v x#)))

(defmacro deff [n v]
  `(def ~n ~v))

(defmacro defun [n args body]
  `(deff ~n (fun ~args ~body)))

;; Bools

(defun truth [t f] t)

(defun falsehood [t f] f)

(defun and [b1 b2]
  (af b1 b2 falsehood))

(defmacro iff [b t f]
  `((af
     ~b
     (fn [_#] ~t)
     (fn [_#] ~f))
    null))

;; Recursion

(defun Y [f]
  ((fn [x] (x x))
   (fn [x]
     (f (fn [y]
          ((x x) y))))))

(defmacro defrec [name binding body]
  `(deff ~name
     (Y
      (fun [~name ~@binding]
           ~body))))

;; Lists

(defun pair [a b]
  (fun [selector nil-val]
       (af selector a b)))

(defun null [selector nil-val]
  nil-val)

(defun null? [p]
  (af p
      (fun [a b] falsehood)
      truth))

(defun car [p]
  (af p
      (fun [f r] f)
      null))

(defun cdr [p]
  (af p
      (fun [f r] r)
      null))

(defmacro if-seq [s fst rst body ncase]
  `(af ~s (fun [~fst ~rst] ~body) ~ncase))

(defmacro when-seq [s fst rst body]
  `(if-seq ~s ~fst ~rst ~body null))

(defrec mapp [f s]
  ;; Strict
  (when-seq s
            fst rst
            (af pair (f fst) (af mapp f rst))))

(defrec repeat-forever [x]
  (af pair x (delay (repeat-forever x))))

;;; numbers

(deff zero null)

(defun inc [n]
  (af pair null n))

(deff zero? null?)

(deff dec cdr)

(defrec an* [n f]
  (fn [x]
    (iff (null? n)
         x
         (f ((af an* (dec n) f) x)))))

(defmacro an [n f]
  `(af an* ~n ~f))

(defrec equals [n1 n2]
  (iff (null? n1)
       (null? n2)
       (iff (null? n2)
            falsehood
            (af equals (dec n1) (dec n2)))))

(defun get-nth [n s]
  (car ((an n cdr) s)))

;; Tape

(defun tape [ls v rs]
  (fn [reader]
    (af reader ls v rs)))

(defun read-tape [t]
  (t (fun [_ v _] v)))

(defun apply-tape [f t]
  (t (fun [ls v rs]
          (af tape ls (f v) rs))))

(defun write-tape [t v]
  (af apply-tape (fn [_] v) t))

(defun left-tape [t]
  (t (fun [ls v rs]
          (when-seq ls
                    fst rst
                    (af tape rst fst (af pair v rs))))))

(defun right-tape [t]
  (t (fun [ls v rs]
          (when-seq rs
                    fst rst
                    (af tape (af pair v ls) fst rst)))))

(deff inc-tape (apply-tape inc))

(deff dec-tape (apply-tape dec))

(deff blank-tape (af tape (repeat-forever zero) zero (repeat-forever zero)))

;; Types

(defmacro defenum [& elements]
  `(do
     ~@(for [e elements]
         `(do
            (defun ~e [~@elements] ~e)
            (defun ~(symbol (str (name e) \?)) [t#]
              (af t# ~@(for [e2 elements]
                         (if (= e e2) `truth `falsehood))))))))

(defmacro deftuple [tname & elements]
  `(do
     (defun ~tname [~@elements]
       (fn [reader#]
         (af reader# ~@elements)))
     ~@(for [e elements]
         `(do
            (defun ~(symbol (str "get-" (name e))) [t#]
              (t# (fun [~@elements] ~e)))
            (deff ~(symbol (str "alter-" (name e)))
              ~(let [f (gensym)
                     t (gensym)
                     new-val (gensym)]
                 `(fun [~f ~t]
                       (lett [~new-val  (~f (~(symbol (str "get-" (name e))) ~t))]
                             (~t
                              (fun [~@elements]
                                   (af ~tname ~@(for [e2 elements] (if (= e2 e) new-val e2)))))))))))))

;; Parsing

(deftuple parse-state parse-instructions loop-stack pairs parse-counter)

(defenum lshift rshift plus minus lbrace rbrace read write)

(defun parse-stepper [state]
  (->>
   (iff (lbrace? (car (get-parse-instructions state)))
        (af alter-loop-stack (pair (get-parse-counter state)) state)
        (iff (rbrace? (car (get-parse-instructions state)))
             (lett [popped-counter (car (get-loop-stack state))]
                   (->> state
                        (af alter-loop-stack cdr)
                        (af alter-pairs (pair (af pair (get-parse-counter state) popped-counter))))) state))
   (af alter-parse-instructions cdr)
   (af alter-parse-counter inc)))

(defrec do-parse-state [state]
  (iff (null? (get-parse-instructions state))
       (get-pairs state)
       (do-parse-state
        (parse-stepper
         state))))

(defrec look-in-pairs [n pairs]
  (when-seq pairs
            fpair rpairs
            (when-seq fpair
                      na nb
                      (iff (af equals n na)
                           (af pair nb null)
                           (iff (af equals n nb)
                                (af pair na null)
                                (af look-in-pairs n rpairs))))))

(defrec make-jump-table [pairs instructions remaining-instructions counter]
  (when-seq remaining-instructions
            _ _
            (af
             pair
             (when-seq (af look-in-pairs counter pairs)
                       jump-to _
                       (af
                        pair
                        jump-to
                        ((an jump-to cdr) instructions)))
             (af make-jump-table pairs instructions (cdr remaining-instructions) (inc counter)))))

;; Instructions

(deftuple brainfuck-state jump-table instructions tape inputs instruction-counter)

(defun id [x] x)

(defun no-print [state]
  (af pair id state))

(defun tape-action [tapefn]
  (fn [state]
    (no-print (af alter-tape tapefn state))))

(deff do-lshift (tape-action left-tape))
(deff do-rshift (tape-action right-tape))
(deff do-plus (tape-action inc-tape))
(deff do-minus (tape-action dec-tape))

(defun do-write [state]
  (lett [v (read-tape (get-tape state))]
        (do
          #_(println "writing" (to-num v))
          (af pair (fn [s] (af pair v s)) state))))

(defun do-read [state]
  (lett [v (car (get-inputs state))]
        (no-print
         (->> state
              (af alter-inputs cdr)
              (af alter-tape (fn [tape]
                               (af write-tape tape v)))))))

(defun do-jump [state]
  (lett [counter (get-instruction-counter state)
         jump-table (get-jump-table state)
         jump-to (af get-nth counter jump-table)]
        (->> state
             (af alter-instructions (fn [_] (cdr jump-to)))
             (af alter-instruction-counter (fn [_] (car jump-to))))))

(defun do-lbrace [state]
  (no-print
   (iff (zero? (read-tape (get-tape state)))
        (do-jump state)
        state)))

(defun do-rbrace [state]
  (no-print
   (iff (zero? (read-tape (get-tape state)))
        state
        (do-jump state))))

;; Running

(defun run-one [state]
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
                            (af alter-instruction-counter inc)))))))

(defrec run-brainfuck-state [state]
  (catch-errors
   (when-seq (run-one state)
             print-output new-state
             (print-output
              (delay
               (run-brainfuck-state new-state))))))

;; Brainfuck

(deff assemble-instructions
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

(defun construct-state [instructions]
  (lett [assembled (assemble-instructions instructions)
         pairs (do-parse-state (af parse-state instructions null null zero))
         jump-table (af make-jump-table pairs assembled assembled zero)]
        (af brainfuck-state jump-table assembled blank-tape null zero)))

(defun insert-inputs [state inputs]
  (af alter-inputs (fn [_] inputs) state))

(defun run-brainfuck [instructions]
  (lett [state (construct-state instructions)]
        (fn [inputs]
          (run-brainfuck-state (af insert-inputs state inputs)))))

;; Interface

(defn from-num [n]
  (loop [n n
         ret zero]
    (if (= n 0)
      ret
      (recur (- n 1) (inc ret)))))

(defn to-bool [b] (af b true false))

(defn from-seq [s]
  (fun [selector nil-val]
       (if (seq s)
         (af selector (first s) (from-seq (rest s)))
         nil-val)))

(defn to-seq [p]
  (lazy-seq
   (af p
       (fun [f r]
            (cons f (to-seq r)))
       nil)))

(defn to-num [n]
  ((an n clojure.core/inc) 0))

;; Brainfuck Interface

(defn lmap [f s]
  (lazy-seq
   (catch-errors
    (when (seq s)
      (cons (f (first s)) (lmap f (rest s)))))))

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

(defn drive-brainfuck [progstring input]
  (let [instructions (parse-brainfuck-string progstring)
        encoded-input (from-seq (lmap #(from-num (long %)) input))
        encoded-output (af run-brainfuck instructions encoded-input)]
    (lmap #(char (to-num %)) (to-seq encoded-output))))

(defn print-brainfuck [progstring input]
  (doseq [c (drive-brainfuck progstring input)]
    (print c)
    (flush)))

(defn get-input-seq []
  (lazy-seq
   (cons (.read (System/in)) (get-input-seq))))

(defn interact-brainfuck [progstring]
  (print-brainfuck progstring (get-input-seq)))
