(ns lambdafuck.core
  (:refer-clojure :exclude [inc zero? delay dec read and]))

(defmacro af [f & args]
  (if (seq args)
    `(af (~f ~(first args)) ~@(rest args))
    f))

(defmacro fun [args body]
  (if (seq args)
    `(fn [~(first args)] (fun ~(rest args) ~body))
    body))

(def zero
  (fn [f]
    (fn [x] x)))

(def one
  (fn [f] f))

(def inc
  (fn [n]
    (fn [f]
      (fn [x]
        (f ((n f) x))))))

(def truth
  (fun [t f] t))

(def falsity
  (fun [t f] f))

(defmacro delay [v]
  `(fn [x#]
     (~v x#)))

(def and
  (fun [b1 b2]
    (af b1 b2 falsity)))

(def zero?
  (fn [n]
    ((n (fn [_] falsity))
     truth)))

(def pair
  (fun [a b]
    (fun [selector nil-val]
      (af selector a b))))

(def null
  (fun [selector nil-val]
    nil-val))

(defmacro an [n f]
  ; in case we change how numbers work
  `(~n ~f))

(def null?
  (fn [p]
    (af p
        (fun [a b] falsity)
        truth)))

(defmacro iff [b t f]
  `((af
     ~b
     (fn [_#] ~t)
     (fn [_#] ~f))
    null))

(defn to-bool [b] (af b true false))

(defn to-num [n]
  ((n clojure.core/inc) 0))

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
        (fun [f r] (cons f (to-seq r)))
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


(def maybe-inc
  (fn [f]
    (fun [n b]
      (af
        f
        (af b (inc n) n)
        truth))))

(def dec
  (fn [n]
    (af
      ((n maybe-inc)
       (fun [n b] n))
      zero
      falsity)))

(def equals
  (fun [n1 n2]
    (af
      and
      (zero? ((n1 dec) n2))
      (zero? ((n2 dec) n1)))))

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

(defmacro when-seq [s fst rst body]
  `(af ~s (fun [~fst ~rst] ~body) null))

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
            (def ~(symbol (str (name e) \?)) (fn [t#] (af t# ~@(for [e2 elements] (if (= e e2) `truth `falsity)))))))))

(defenum lshift rshift plus minus lbrace rbrace read write)

(defmacro deftuple [tname & elements]
  `(do
     (def ~tname
       (fun [~@elements]
         (fn [reader#]
           (println "got a state reader")
           (do
             ~@(for [e elements]
                 `(println ~e)))
           (println reader#)
           (let [res# (try
                        (af reader# ~@elements)
                        (catch Exception e#
                          (clojure.tools.logging/error e# "failed")
                          (throw e#)
                          )
                        )]
             (println "read the state")
             res#))))
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
                    ((fn [~new-val]
                       (~t
                         (fun [~@elements]
                           (af ~tname ~@(for [e2 elements] (if (= e2 e) new-val e2))))))
                     (~f (~(symbol (str "get-" (name e))) ~t))))))))))

(deftuple brainfuck-state jump-table instructions tape inputs instruction-counter)

(deftuple parse-state parse-instructions loop-stack pairs parse-counter)

(defmacro lett [bind body]
  (if (seq bind)
    `((fn [~(first bind)]
        (lett ~(drop 2 bind) ~body))
      ~(second bind))
    body))

(def parse-stepper
  (fn [state]
    (->>
      (iff (lbrace? (car (get-parse-instructions state)))
        (af alter-loop-stack (pair (get-parse-counter state)) state)
        (iff (rbrace? (car (get-parse-instructions state)))
          (lett [popped-counter (car (get-loop-stack state))]
            (->> state
                 (af alter-loop-stack cdr)
                 (af alter-pairs (pair (af pair (get-parse-counter state) popped-counter)))))state))
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
    (println "running a single step")
    (lett [ins (car (get-instructions state))]
      (->> state
           ins
           (af alter-instructions cdr)
           (af alter-instruction-counter inc)))))

(defrec run-brainfuck-state
  (fn [state]
    (when-seq (run-one state)
      print-output new-state
      (print-output
        (delay
          (run-brainfuck-state new-state))))))

(def id (fn [x] x))

(def tape-action
  (fn [tapefn]
    (fn [state]
      (println "doing a tape action")
      (af pair id (af alter-tape tapefn state)))))

(def do-lshift (tape-action left-tape))
(def do-rshift (tape-action right-tape))
(def do-plus (tape-action inc-tape))
(def do-minus (tape-action dec-tape))

(def do-write
  (fn [state]
    (lett [v (read-tape (get-tape state))]
      (af pair (fn [s] (af pair v s)) state))))

(def do-read
  (fn [state]
    (lett [v (car (get-inputs state))]
      (af
        pair
        id
        (->> state
          (af alter-inputs cdr)
          (af alter-tape (fn [tape]
                           (write-tape tape v))))))))

(def do-jump
  (fn [state]
    (println "jumping")
    (lett [counter (get-instruction-counter state)
           jump-table (get-jump-table state)
           jump-to (car ((an counter cdr) jump-table))]
      (->> state
           (af alter-instructions (fn [_] (cdr jump-to)))
           (af alter-instruction-counter (fn [_] (car jump-to)))))))

(def do-lbrace
  (fn [state]
    (iff (zero? (read-tape (get-tape state)))
      (do-jump state)
      state)))

(def do-rbrace
  (fn [state]
    (iff (zero? (read-tape (get-tape state)))
      state
      (do-jump state))))

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
  (fun [pairs instructions counter]
    (iff (null? instructions)
      null
      (af
        pair
        (when-seq (af look-in-pairs counter pairs)
          jump-to _
          (af
            pair
            jump-to
            ((an jump-to cdr) instructions)))
        (af make-jump-table pairs (cdr instructions) (inc counter))))))

(def construct-state
  (fun [instructions inputs]
    (lett [assembled (assemble-instructions instructions)
           pairs (do-parse-state (af parse-state instructions null null zero))
           jump-table (af make-jump-table pairs assembled zero)
           _ (println "constructed state")]
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
    (when (seq s)
      (cons (f (first s)) (lmap f (rest s))))))

(defn from-num [n]
  (if (= n 0)
    zero
    (inc (from-num (- n 1)))))

(defn drive-brainfuck [progstring input]
  (let [instructions (parse-brainfuck-string progstring)
        encoded-input (from-seq (lmap #(from-num (long %)) input))
        encoded-output (af run-brainfuck instructions encoded-input)]
    (lmap #(char (to-num %)) (to-seq encoded-output))))

(comment
  (require 'lanterna.screen)

  (drive-brainfuck "++++++++++[>+++++++>++++++++++>+++>+<<<<-]>++.>+.+++++++..+++.>++.<<+++++++++++++++.>.+++.------.--------.>+.>." ())

  (def scr (lanterna.screen/get-screen))

  (lanterna.screen/start scr)

  (lanterna.screen/get-key-blocking scr)

  (long \a))

(char 97)
