forbid(
  principal in a::"",
  action,
  resource
) when {
  true && (!((context == false) == (duration("0ms"))))
};
