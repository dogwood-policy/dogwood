permit(
  principal,
  action in [Action::"action"],
  resource is a
) when {
  ((true && (if (if (if false then true else false) then (if true then true else true) else ((ip("127.0.3.172/11")).isLoopback())) then false else false)) && false) && false
};
