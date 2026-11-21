static clean_obj* clean_push_codepoint_borrowed(clean_obj* s, clean_obj* c) {
  uint32_t cp = clean_unbox_uint32(c);
  size_t len = clean_string_len(s);
  if (len > SIZE_MAX - 5) { clean_panic("l_String_push: string size overflow"); }
  char* buf = (char*)malloc(len + 4 + 1);
  if (!buf) { clean_panic("l_String_push: allocation failed"); }
  memcpy(buf, clean_string_data(s), len);
  size_t k = len;
  if (cp < 0x80) { buf[k++] = (char)cp; }
  else if (cp < 0x800) {
    buf[k++] = (char)(0xC0 | (cp >> 6));
    buf[k++] = (char)(0x80 | (cp & 0x3F));
  } else if (cp < 0x10000) {
    buf[k++] = (char)(0xE0 | (cp >> 12));
    buf[k++] = (char)(0x80 | ((cp >> 6) & 0x3F));
    buf[k++] = (char)(0x80 | (cp & 0x3F));
  } else {
    buf[k++] = (char)(0xF0 | (cp >> 18));
    buf[k++] = (char)(0x80 | ((cp >> 12) & 0x3F));
    buf[k++] = (char)(0x80 | ((cp >> 6) & 0x3F));
    buf[k++] = (char)(0x80 | (cp & 0x3F));
  }
  buf[k] = 0;
  clean_obj* r = clean_mk_string_from_bytes(buf, k);
  free(buf);
  return r;
}
