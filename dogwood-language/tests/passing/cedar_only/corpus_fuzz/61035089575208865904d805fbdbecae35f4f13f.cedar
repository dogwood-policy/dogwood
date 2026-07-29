forbid(
  principal is jz::a,
  action == jz::Action::"action",
  resource in jz::a::">>>"
) when {
  (true && (if ((if true then false else false) || ((ip("2001:948:7a3a:993b:993e:3e3e:3e3e:c1c1/126")).isInRange(ip("5ff:af0f:120:6e61:6962:6544:ffff:ff69/105")))) then (([(datetime("4975-02-08T15:13:13.087Z")).offset(duration("-2864783874392024842d8825501086245354087h"))].containsAll([ip("5353:5353:5353:5353:5353:5353:af67:ffff/83")])) && ((decimal("882550108624535.4106")).lessThan(decimal("286478387695216.2049")))) else (({"": ip("7a7a:7a7a:41ff:3633:3333:3333:38aa:aa72/51")}[""]).isInRange(ip("0.0.0.0"))))) && false
};
