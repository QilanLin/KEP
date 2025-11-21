# Preprocessing class: FSSSSMSSSSSNFFN.
# Scheduled 1 strats onto 1 cores with 3 seconds (3 total)
# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 3s (1) cores
# G-E--_302_C18_F1_URBAN_RG_S04BN with pid 12756 completed with status 1
# Result found by G-E--_302_C18_F1_URBAN_RG_S04BN
# Preprocessing class: FSSSSMSSSSSNFFN.
# Scheduled 1 strats onto 1 cores with 3 seconds (3 total)
# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 3s (1) cores
# No SInE strategy applied
# Search class: FUUSF-FFSF22-SFFFFFNN
# partial match(1): FUUNF-FFSF22-SFFFFFNN
# Scheduled 2 strats onto 1 cores with 3 seconds (3 total)
# Starting SAT001_MinMin_p005000_rr_RG with 2s (1) cores
# SAT001_MinMin_p005000_rr_RG with pid 12757 completed with status 1
# Result found by SAT001_MinMin_p005000_rr_RG
# Preprocessing class: FSSSSMSSSSSNFFN.
# Scheduled 1 strats onto 1 cores with 3 seconds (3 total)
# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 3s (1) cores
# No SInE strategy applied
# Search class: FUUSF-FFSF22-SFFFFFNN
# partial match(1): FUUNF-FFSF22-SFFFFFNN
# Scheduled 2 strats onto 1 cores with 3 seconds (3 total)
# Starting SAT001_MinMin_p005000_rr_RG with 2s (1) cores
# Presaturation interreduction done

# No proof found!
# SZS status CounterSatisfiable
# SZS output start Saturation
tff(decl_sort1, type, a: $tType).
tff(decl_sort2, type, bool: $tType).
tff(decl_22, type, plus_plus_a: (a * a) > a).
tff(decl_23, type, zero_zero_a: a).
tff(decl_24, type, fFalse: bool).
tff(decl_25, type, fTrue: bool).
tff(decl_26, type, pp: bool > $o).
tff(decl_27, type, x: a).
tff(help_pp_1_1_U, axiom, ~(pp(fFalse)), file('/Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob4850772_1.p', help_pp_1_1_U)).
tff(conj_0, conjecture, plus_plus_a(x,zero_zero_a)=x, file('/Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob4850772_1.p', conj_0)).
tff(help_pp_2_1_U, axiom, pp(fTrue), file('/Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob4850772_1.p', help_pp_2_1_U)).
tff(c_0_3, plain, ~pp(fFalse), inference(fof_simplification,[status(thm)],[help_pp_1_1_U])).
tff(c_0_4, negated_conjecture, plus_plus_a(x,zero_zero_a)!=x, inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[conj_0])])).
tff(c_0_5, plain, ~pp(fFalse), inference(fof_nnf,[status(thm)],[c_0_3])).
tff(c_0_6, negated_conjecture, plus_plus_a(x,zero_zero_a)!=x, inference(fof_nnf,[status(thm)],[c_0_4])).
tcf(c_0_7, plain, ~pp(fFalse), inference(split_conjunct,[status(thm)],[c_0_5]), ['final']).
tcf(c_0_8, negated_conjecture, plus_plus_a(x,zero_zero_a)!=x, inference(split_conjunct,[status(thm)],[c_0_6]), ['final']).
tcf(c_0_9, plain, pp(fTrue), inference(split_conjunct,[status(thm)],[help_pp_2_1_U]), ['final']).
# SZS output end Saturation