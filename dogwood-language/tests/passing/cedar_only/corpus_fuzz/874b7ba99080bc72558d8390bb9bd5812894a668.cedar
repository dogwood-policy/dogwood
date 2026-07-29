@r("")
forbid(
  principal,
  action in [Action::""],
  resource
) when {
  ((true && (principal in [a::""])) && (a::"" in a::"")) && ((({"": {"": ip("255.255.255.255/24")}}[""])[""]).isMulticast())
};
