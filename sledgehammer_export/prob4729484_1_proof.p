# Preprocessing class: FSSSSMSSSSSNFFN.
# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)
# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 5s (1) cores
# G-E--_302_C18_F1_URBAN_RG_S04BN with pid 12188 completed with status 0
# Result found by G-E--_302_C18_F1_URBAN_RG_S04BN
# Preprocessing class: FSSSSMSSSSSNFFN.
# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)
# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 5s (1) cores
# No SInE strategy applied
# Search class: FUUNF-FFSF00-SFFFFFNN
# Scheduled 3 strats onto 1 cores with 5 seconds (5 total)
# Starting SAT001_MinMin_p005000_rr_RG with 3s (1) cores
# SAT001_MinMin_p005000_rr_RG with pid 12189 completed with status 0
# Result found by SAT001_MinMin_p005000_rr_RG
# Preprocessing class: FSSSSMSSSSSNFFN.
# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)
# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 5s (1) cores
# No SInE strategy applied
# Search class: FUUNF-FFSF00-SFFFFFNN
# Scheduled 3 strats onto 1 cores with 5 seconds (5 total)
# Starting SAT001_MinMin_p005000_rr_RG with 3s (1) cores
# Presaturation interreduction done

# Proof found!
# SZS status Theorem
# SZS output start CNFRefutation
tff(decl_sort1, type, a: $tType).
tff(decl_22, type, p: a > $o).
tff(decl_23, type, esk1_0: a).
tff(conj_0, conjecture, ![X1:a]:((~(p(X1))|p(X1))), file('/Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob4729484_1.p', conj_0)).
tff(c_0_1, negated_conjecture, ~(![X1:a]:((~p(X1)|p(X1)))), inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[conj_0])])).
tff(c_0_2, negated_conjecture, (p(esk1_0)&~p(esk1_0)), inference(fof_nnf,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_1])])])])).
tcf(c_0_3, negated_conjecture, ~p(esk1_0), inference(split_conjunct,[status(thm)],[c_0_2])).
tcf(c_0_4, negated_conjecture, p(esk1_0), inference(split_conjunct,[status(thm)],[c_0_2])).
cnf(c_0_5, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_3, c_0_4])]), ['proof']).
# SZS output end CNFRefutation