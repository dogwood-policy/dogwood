permit(
  principal in a::"",
  action in [Action::"\u{7}\u{7}\u{7}\u{7}\u{7}\u{7}\u{7}\u{7}\u{7}\u{7}"],
  resource is a
) when {
  true && (if ((context[""]).isLoopback()) then ((resource in resource) || (if true then true else false)) else (true == false))
};
