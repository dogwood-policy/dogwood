forbid(
  principal == a::"",
  action in [],
  resource
) when {
  (true && (if (if (a::"" in principal) then (resource in resource) else (resource in resource)) then false else false)) && false
};
