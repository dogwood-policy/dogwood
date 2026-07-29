forbid(
  principal is a in a::"",
  action,
  resource in a::""
) when {
  (true && ((if ((duration("7948146475450531968h")) < (duration("0ms"))) then principal else principal) is a)) && false
};
