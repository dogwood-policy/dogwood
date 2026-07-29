@A("")
@B("")
@_RRR("")
@p("")
@r("")
@r3("")
@v("")
@x("")
forbid(
  principal,
  action in [Action::"action"],
  resource == a::"\0\0"
) when {
  ((true && ((({"": {"": ip("9999:9999:9999:9999:9999:9999:9999:9999/24")}}[""])[""]).isIpv4())) && true) && true
};
