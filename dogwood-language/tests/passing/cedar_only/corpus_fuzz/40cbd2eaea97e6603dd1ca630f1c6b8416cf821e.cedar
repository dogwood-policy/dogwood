@p("")
forbid(
  principal == t::"",
  action == Action::"action",
  resource in t::"^[\0"
) when {
  ((true && ((({"": {"": ip("232.255.91.94")}}[""])[""]).isMulticast())) && ((principal in t::"^[\0") || false)) && true
};
