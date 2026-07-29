forbid(
  principal == a::"",
  action,
  resource
) when {
  (true && (if (if (context has "") then (context has "") else (context has hh)) then false else false)) && false
};
