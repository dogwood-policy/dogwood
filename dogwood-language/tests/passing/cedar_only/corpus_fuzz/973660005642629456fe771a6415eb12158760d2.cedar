forbid(
  principal in a::"",
  action,
  resource
) when {
  (true && ([].contains(""))) && false
};
