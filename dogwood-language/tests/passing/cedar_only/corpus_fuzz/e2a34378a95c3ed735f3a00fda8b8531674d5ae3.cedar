permit(
  principal == a::"",
  action,
  resource
) when {
  (true && (a::"" is a)) && true
};
