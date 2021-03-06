// Haddock JavaScript utilities

const rspace = /\s\s+/g,
    rtrim = /^\s+|\s+$/g;

function spaced(s: string) { return (" " + s + " ").replace(rspace, " "); }
function trim(s: string)   { return s.replace(rtrim, ""); }

function hasClass(elem: Element, value: string) {
  const className = spaced(elem.className || "");
  return className.indexOf( " " + value + " " ) >= 0;
}

function addClass(elem: Element, value: string) {
  const className = spaced(elem.className || "");
  if ( className.indexOf( " " + value + " " ) < 0 ) {
    elem.className = trim(className + " " + value);
  }
}

function removeClass(elem: Element, value: string) {
  let className = spaced(elem.className || "");
  className = className.replace(" " + value + " ", " ");
  elem.className = trim(className);
}

function toggleClass(elem: Element, valueOn: string, valueOff: string, bool?: boolean): boolean {
  if (bool == null) { bool = ! hasClass(elem, valueOn); }
  if (bool) {
    removeClass(elem, valueOff);
    addClass(elem, valueOn);
  }
  else {
    removeClass(elem, valueOn);
    addClass(elem, valueOff);
  }
  return bool;
}


function makeClassToggle(valueOn: string, valueOff: string): (elem: Element, bool?: boolean) => boolean {
  return function(elem, bool) {
    return toggleClass(elem, valueOn, valueOff, bool);
  }
}

const toggleShow = makeClassToggle("show", "hide");
const toggleCollapser = makeClassToggle("collapser", "expander");

function toggleSection(id: string): boolean {
  const b = toggleShow(document.getElementById("section." + id) as Element);
  toggleCollapser(document.getElementById("control." + id) as Element, b);
  rememberCollapsed(id);
  return b;
}

// TODO: get rid of global variables
if (typeof window !== 'undefined') {
  (window as any).toggleSection = toggleSection;
}

const collapsed: { [id: string]: boolean } = {};
function rememberCollapsed(id: string) {
  if(collapsed[id])
    delete collapsed[id]
  else
    collapsed[id] = true;

  const sections: string[] = [];
  for(let i in collapsed) {
    if(collapsed.hasOwnProperty(i))
      sections.push(i);
  }
  // cookie specific to this page; don't use setCookie which sets path=/
  document.cookie = "collapsed=" + encodeURIComponent(sections.join('+'));
}

export function restoreCollapsed() {
  const cookie = getCookie("collapsed");
  if(!cookie)
    return;

  const ids = cookie.split('+');
  for(const i in ids)
  {
    if(document.getElementById("section." + ids[i]))
      toggleSection(ids[i]);
  }
}

function setCookie(name: string, value: string) {
  document.cookie = name + "=" + encodeURIComponent(value) + ";path=/;";
}

function clearCookie(name: string) {
  document.cookie = name + "=;path=/;expires=Thu, 01-Jan-1970 00:00:01 GMT;";
}

function getCookie(name: string) {
  const nameEQ = name + "=";
  const ca = document.cookie.split(';');
  for (let i = 0; i < ca.length; i++) {
    let c = ca[i];
    while (c.charAt(0)==' ') c = c.substring(1,c.length);
    if (c.indexOf(nameEQ) == 0) {
      return decodeURIComponent(c.substring(nameEQ.length,c.length));
    }
  }
  return null;
}

function addMenuItem(html: string) {
  const menu = document.getElementById("page-menu");
  if (menu && menu.firstChild) {
    const btn = menu.firstChild.cloneNode(false) as Element;
    btn.innerHTML = html;
    menu.appendChild(btn);
  }
}

function styles(): HTMLLinkElement[] {
  const es = Array.prototype.slice.call(document.getElementsByTagName("link"));
  return es.filter((a: HTMLLinkElement) => a.rel.indexOf("style") != -1 && a.title);
}

export function addStyleMenu() {
  const as = styles();
  let btns = "";
  as.forEach((a) => {
    btns += "<li><a href='#' onclick=\"setActiveStyleSheet('"
      + a.title + "'); return false;\">"
      + a.title + "</a></li>"
  });
  if (as.length > 1) {
    const h = "<div id='style-menu-holder'>"
      + "<a href='#' onclick='styleMenu(); return false;'>Style &#9662;</a>"
      + "<ul id='style-menu' class='hide'>" + btns + "</ul>"
      + "</div>";
    addMenuItem(h);
  }
}

function setActiveStyleSheet(title: string) {
  const as = styles();
  let found: null | HTMLLinkElement = null;
  for(let i = 0; i < as.length; i++) {
    const a = as[i];
    a.disabled = true;
          // need to do this always, some browsers are edge triggered
    if(a.title == title) {
      found = a;
    }
  }
  if (found) {
    found.disabled = false;
    setCookie("haddock-style", title);
  }
  else {
    as[0].disabled = false;
    clearCookie("haddock-style");
  }
  styleMenu(false);
}

export function resetStyle() {
  const s = getCookie("haddock-style");
  if (s) setActiveStyleSheet(s);
}

function styleMenu(show?: boolean) {
  const m = document.getElementById('style-menu');
  if (m) toggleShow(m, show);
}