% done 0 iterations in 0.006s
% SZS status Theorem for '/Users/linqilan/Downloads/KEP AWS/sledgehammer_export/prob4729486_1.p'
% SZS output start Refutation
thf(a_type, type, a: $tType).
thf(conj_0, conjecture, (![X:a]: ( $true ))).
thf(zf_stmt_0, negated_conjecture, (~( ![X:a]: ( $true ) )),
  inference('cnf.neg', [status(esa)], [conj_0])).
thf(zip_derived_cl0, plain, ($false),
    inference('cnf', [status(esa)], [zf_stmt_0])).

% SZS output end Refutation