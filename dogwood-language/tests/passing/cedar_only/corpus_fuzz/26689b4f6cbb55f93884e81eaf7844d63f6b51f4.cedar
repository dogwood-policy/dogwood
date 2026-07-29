forbid(
  principal == a::"",
  action,
  resource
) when {
  (true && (false == (a::"" has ""))) && (a::"" has ",")
};
