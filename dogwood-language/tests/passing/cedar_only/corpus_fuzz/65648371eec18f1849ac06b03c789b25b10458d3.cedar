@A("")
permit(
  principal in a::"",
  action,
  resource == a::":?!!"
) when {
  true
};
