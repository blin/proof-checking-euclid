Ltac one_of_disjunct H :=
	repeat (exact H || (left; exact H) || right).
