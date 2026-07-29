forbid(
  principal == a::":",
  action,
  resource
) when {
  ((true && (({"": ip("80.80.83.153")}[""]).isMulticast())) && false) && false
};
