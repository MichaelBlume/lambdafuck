(ns lambdafuck.core-test
  (:require [clojure.test :refer :all]
            [lambdafuck.core :refer [drive-brainfuck]]
            [clojure.java.io :refer [resource]]))

(deftest test-drive
  (is (= (seq "Primes up to: 2 3 5 \n")
         (drive-brainfuck
          (slurp (resource "PRIME.BF"))
          "6\n"))))
