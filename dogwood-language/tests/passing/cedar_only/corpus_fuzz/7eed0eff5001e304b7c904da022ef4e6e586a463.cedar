permit(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && ({"F5j000GebGGA\u{1}\0": action is a}["F5j000GebGGA\u{1}\0"])) && (context == context)
};
