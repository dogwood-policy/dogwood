@G0000000("")
forbid(
  principal in a::"                                            ",
  action in [Action::"action"],
  resource in a::"                                            "
) when {
  (true && (if (if (principal in principal) then (principal in principal) else (principal in principal)) then (a::"                                            " in principal) else (a::"                                            " is a))) && (if (if (if false then false else false) then false else false) then false else true)
};
