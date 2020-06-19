(ns lambdafuck.main
  (:require [lambdafuck.core :as bf])
  (:gen-class))

(defn -main [source-file]
  (println "starting interpreter")
  (let [interpreter (bf/start-brainfuck-interpreter (slurp source-file))]
    (println "running program")
    (bf/interact-brainfuck-interpreter interpreter)))
