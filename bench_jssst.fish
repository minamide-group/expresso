#!/usr/bin/fish
for file in constraints/bench/{indexof2_sat,indexof2_unsat,deleteall,substr_equiv,inverse_sat,inverse_unsat}
    echo ";; $file ;;"
    time java -jar target/scala-2.13/expresso-assembly-0.3.0-SNAPSHOT.jar $file.smt2 jssst &| python3 summary_jssst.py
end
