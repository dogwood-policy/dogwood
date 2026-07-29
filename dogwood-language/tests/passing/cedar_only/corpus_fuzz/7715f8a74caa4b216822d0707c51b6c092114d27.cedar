permit(
  principal == a::"\0\0\0\0\0\0\0:*\0\0\0",
  action,
  resource
) when {
  true && ((({"": context}[""])[""]).lessThan(context["[\u{8}"]))
};
