permit(
  principal,
  action == Action::"action",
  resource
) when {
  ((true && ((({"": {"": ip("::ffff:255.255.255.0")}}[""])[""]).isMulticast())) && false) && false
};
