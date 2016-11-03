sig People {}
sig Luca extends People{}

sig Edo extends People{}

assert EdoeLuca { all p:People,e:Edo, l:Luca |e in p or l in p}

check EdoeLuca
