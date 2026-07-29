forbid(
  principal == a::"",
  action in [Action::"action"],
  resource
) when {
  true && ((!((ip("0.0.29.0/24")).isInRange(ip("62.62.62.62")))) || (if (if false then false else false) then (if false then false else false) else (if false then false else false)))
};
