From iris.algebra Require Import gmap.
Ltac inv_map_in :=
       match goal with
         | H : (?i, ?y) ∈ map ?f ?l |- _ => apply elem_of_list_In in H;
                                           apply in_map_iff in H;
                                           destruct H;
                                           destruct H
         |  |- (?i, ?y) ∈ map ?f ?l => apply elem_of_list_In;
                                      apply in_map_iff;
                                      try split;eauto
         | H : (?x) ∈ map ?f ?l |- _ => apply elem_of_list_In in H;
                                       apply in_map_iff in H;
                                       destruct H;
                                       destruct H
         |  |- (?x) ∈ map ?f ?l => apply elem_of_list_In;
                                  apply in_map_iff;
                                  try split;eauto
       end.
