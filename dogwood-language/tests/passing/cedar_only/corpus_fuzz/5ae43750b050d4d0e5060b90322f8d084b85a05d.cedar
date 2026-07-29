forbid(
  principal is a in a::"zz",
  action in [Action::"action"],
  resource is a in a::"zz"
) when {
  ((true && ((({"": ip("154.154.154.154")}[""]).isLoopback()) && true)) && false) && false
};
