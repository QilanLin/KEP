# Preprocessing class: FSSSSMSSSSSNFFN.
# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)
# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 5s (1) cores
# G-E--_302_C18_F1_URBAN_RG_S04BN with pid 12252 completed with status 1
# Result found by G-E--_302_C18_F1_URBAN_RG_S04BN
# Preprocessing class: FSSSSMSSSSSNFFN.
# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)
# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 5s (1) cores
# No SInE strategy applied
# Search class: FUUPF-FFSF22-SFFFFFNN
# Scheduled 3 strats onto 1 cores with 5 seconds (5 total)
# Starting SAT001_MinMin_p005000_rr_RG with 3s (1) cores
# SAT001_MinMin_p005000_rr_RG with pid 12253 completed with status 1
# Result found by SAT001_MinMin_p005000_rr_RG
# Preprocessing class: FSSSSMSSSSSNFFN.
# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)
# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 5s (1) cores
# No SInE strategy applied
# Search class: FUUPF-FFSF22-SFFFFFNN
# Scheduled 3 strats onto 1 cores with 5 seconds (5 total)
# Starting SAT001_MinMin_p005000_rr_RG with 3s (1) cores
# Presaturation interreduction done

# No proof found!
# SZS status CounterSatisfiable
# SZS output start Saturation
tff(decl_sort1, type, a: $tType).
tff(decl_22, type, plus_plus_a: (a * a) > a).
tff(decl_23, type, zero_zero_a: a).
tff(decl_24, type, x: a).
tff(conj_0, conjecture, plus_plus_a(x,zero_zero_a)=x, file('/Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob4748530_1.p', conj_0)).
tff(c_0_1, negated_conjecture, plus_plus_a(x,zero_zero_a)!=x, inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[conj_0])])).
tff(c_0_2, negated_conjecture, plus_plus_a(x,zero_zero_a)!=x, inference(fof_nnf,[status(thm)],[c_0_1])).
tcf(c_0_3, negated_conjecture, plus_plus_a(x,zero_zero_a)!=x, inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).
# SZS output end Saturation