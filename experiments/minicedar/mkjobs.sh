bugs="and-true-left or-false-left not-not ite-bool-id add-zero and-true-right mul-zero eq-refl ite-same and-false-right sub-self record-access and-commute neg-neg record-last eq-commute add-commute"
for b in $bugs; do for g in mc mcv; do for be in io fuzz; do for t in 1 2 3 4 5; do echo "$b $g $be $t"; done; done; done; done
