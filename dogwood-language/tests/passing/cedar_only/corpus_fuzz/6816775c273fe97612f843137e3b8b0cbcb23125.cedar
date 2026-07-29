forbid(
  principal in a::"\u{18}",
  action in [Action::"action"],
  resource in a::"\u{18}"
) when {
  (true && (if (if (principal is a) then (resource is a) else (if false then false else false)) then (if (if false then false else false) then (if false then false else false) else (if false then false else false)) else (({"hhhL\0": resource}["hhhL\0"]) is a))) && (!((-15198184) <= 255))
};
