!function(e){function t(t){for(var n,i,o=t[0],a=t[1],c=0,l=[];c<o.length;c++)i=o[c],Object.prototype.hasOwnProperty.call(r,i)&&r[i]&&l.push(r[i][0]),r[i]=0;for(n in a)Object.prototype.hasOwnProperty.call(a,n)&&(e[n]=a[n]);for(s&&s(t);l.length;)l.shift()()}var n={},r={0:0};var i={};var o={6:function(){return{"./index_bg.js":{__wbg_alert_6fa194cbc9646d56:function(e,t){return n[5].exports.a(e,t)},__wbg_log_ba42a6b973b698fa:function(e,t){return n[5].exports.b(e,t)},__wbindgen_json_parse:function(e,t){return n[5].exports.c(e,t)}}}}};function a(t){if(n[t])return n[t].exports;var r=n[t]={i:t,l:!1,exports:{}};return e[t].call(r.exports,r,r.exports,a),r.l=!0,r.exports}a.e=function(e){var t=[],n=r[e];if(0!==n)if(n)t.push(n[2]);else{var c=new Promise((function(t,i){n=r[e]=[t,i]}));t.push(n[2]=c);var l,u=document.createElement("script");u.charset="utf-8",u.timeout=120,a.nc&&u.setAttribute("nonce",a.nc),u.src=function(e){return a.p+""+e+".index.js"}(e);var s=new Error;l=function(t){u.onerror=u.onload=null,clearTimeout(d);var n=r[e];if(0!==n){if(n){var i=t&&("load"===t.type?"missing":t.type),o=t&&t.target&&t.target.src;s.message="Loading chunk "+e+" failed.\n("+i+": "+o+")",s.name="ChunkLoadError",s.type=i,s.request=o,n[1](s)}r[e]=void 0}};var d=setTimeout((function(){l({type:"timeout",target:u})}),12e4);u.onerror=u.onload=l,document.head.appendChild(u)}return({1:[6]}[e]||[]).forEach((function(e){var n=i[e];if(n)t.push(n);else{var r,c=o[e](),l=fetch(a.p+""+{6:"9efa135124674fda0927"}[e]+".module.wasm");if(c instanceof Promise&&"function"==typeof WebAssembly.compileStreaming)r=Promise.all([WebAssembly.compileStreaming(l),c]).then((function(e){return WebAssembly.instantiate(e[0],e[1])}));else if("function"==typeof WebAssembly.instantiateStreaming)r=WebAssembly.instantiateStreaming(l,c);else{r=l.then((function(e){return e.arrayBuffer()})).then((function(e){return WebAssembly.instantiate(e,c)}))}t.push(i[e]=r.then((function(t){return a.w[e]=(t.instance||t).exports})))}})),Promise.all(t)},a.m=e,a.c=n,a.d=function(e,t,n){a.o(e,t)||Object.defineProperty(e,t,{enumerable:!0,get:n})},a.r=function(e){"undefined"!=typeof Symbol&&Symbol.toStringTag&&Object.defineProperty(e,Symbol.toStringTag,{value:"Module"}),Object.defineProperty(e,"__esModule",{value:!0})},a.t=function(e,t){if(1&t&&(e=a(e)),8&t)return e;if(4&t&&"object"==typeof e&&e&&e.__esModule)return e;var n=Object.create(null);if(a.r(n),Object.defineProperty(n,"default",{enumerable:!0,value:e}),2&t&&"string"!=typeof e)for(var r in e)a.d(n,r,function(t){return e[t]}.bind(null,r));return n},a.n=function(e){var t=e&&e.__esModule?function(){return e.default}:function(){return e};return a.d(t,"a",t),t},a.o=function(e,t){return Object.prototype.hasOwnProperty.call(e,t)},a.p="",a.oe=function(e){throw console.error(e),e},a.w={};var c=window.webpackJsonp=window.webpackJsonp||[],l=c.push.bind(c);c.push=t,c=c.slice();for(var u=0;u<c.length;u++)t(c[u]);var s=l;a(a.s=4)}([function(e,t,n){"use strict";var r=n(2),i=n.n(r)()((function(e){return e[1]}));i.push([e.i,'/* Remove default bullets */\nul {\n  list-style-type: none;\n  padding-left: 20px;\n}\n\n/* Style the caret/arrow */\n.caret {\n  cursor: pointer;\n  user-select: none; /* Prevent text selection */\n}\n\n/* Create the caret/arrow with a unicode, and style it */\n.caret::before {\n  content: "\\25B6";\n  color: black;\n  display: inline-block;\n  margin-right: 6px;\n}\n\n/* Rotate the caret/arrow icon when clicked on (using JavaScript) */\n.caret-down::before {\n  transform: rotate(90deg);\n}\n\n/* Hide the nested list */\n.nested {\n  display: none;\n}\n\n/* Show the nested list when the user clicks on the caret/arrow (with JavaScript) */\n.active {\n  display: block;\n}\n',""]),t.a=i},function(e,t,n){"use strict";var r,i=function(){return void 0===r&&(r=Boolean(window&&document&&document.all&&!window.atob)),r},o=function(){var e={};return function(t){if(void 0===e[t]){var n=document.querySelector(t);if(window.HTMLIFrameElement&&n instanceof window.HTMLIFrameElement)try{n=n.contentDocument.head}catch(e){n=null}e[t]=n}return e[t]}}(),a=[];function c(e){for(var t=-1,n=0;n<a.length;n++)if(a[n].identifier===e){t=n;break}return t}function l(e,t){for(var n={},r=[],i=0;i<e.length;i++){var o=e[i],l=t.base?o[0]+t.base:o[0],u=n[l]||0,s="".concat(l," ").concat(u);n[l]=u+1;var d=c(s),f={css:o[1],media:o[2],sourceMap:o[3]};-1!==d?(a[d].references++,a[d].updater(f)):a.push({identifier:s,updater:v(f,t),references:1}),r.push(s)}return r}function u(e){var t=document.createElement("style"),r=e.attributes||{};if(void 0===r.nonce){var i=n.nc;i&&(r.nonce=i)}if(Object.keys(r).forEach((function(e){t.setAttribute(e,r[e])})),"function"==typeof e.insert)e.insert(t);else{var a=o(e.insert||"head");if(!a)throw new Error("Couldn't find a style target. This probably means that the value for the 'insert' parameter is invalid.");a.appendChild(t)}return t}var s,d=(s=[],function(e,t){return s[e]=t,s.filter(Boolean).join("\n")});function f(e,t,n,r){var i=n?"":r.media?"@media ".concat(r.media," {").concat(r.css,"}"):r.css;if(e.styleSheet)e.styleSheet.cssText=d(t,i);else{var o=document.createTextNode(i),a=e.childNodes;a[t]&&e.removeChild(a[t]),a.length?e.insertBefore(o,a[t]):e.appendChild(o)}}function p(e,t,n){var r=n.css,i=n.media,o=n.sourceMap;if(i?e.setAttribute("media",i):e.removeAttribute("media"),o&&"undefined"!=typeof btoa&&(r+="\n/*# sourceMappingURL=data:application/json;base64,".concat(btoa(unescape(encodeURIComponent(JSON.stringify(o))))," */")),e.styleSheet)e.styleSheet.cssText=r;else{for(;e.firstChild;)e.removeChild(e.firstChild);e.appendChild(document.createTextNode(r))}}var m=null,h=0;function v(e,t){var n,r,i;if(t.singleton){var o=h++;n=m||(m=u(t)),r=f.bind(null,n,o,!1),i=f.bind(null,n,o,!0)}else n=u(t),r=p.bind(null,n,t),i=function(){!function(e){if(null===e.parentNode)return!1;e.parentNode.removeChild(e)}(n)};return r(e),function(t){if(t){if(t.css===e.css&&t.media===e.media&&t.sourceMap===e.sourceMap)return;r(e=t)}else i()}}e.exports=function(e,t){(t=t||{}).singleton||"boolean"==typeof t.singleton||(t.singleton=i());var n=l(e=e||[],t);return function(e){if(e=e||[],"[object Array]"===Object.prototype.toString.call(e)){for(var r=0;r<n.length;r++){var i=c(n[r]);a[i].references--}for(var o=l(e,t),u=0;u<n.length;u++){var s=c(n[u]);0===a[s].references&&(a[s].updater(),a.splice(s,1))}n=o}}}},function(e,t,n){"use strict";e.exports=function(e){var t=[];return t.toString=function(){return this.map((function(t){var n=e(t);return t[2]?"@media ".concat(t[2]," {").concat(n,"}"):n})).join("")},t.i=function(e,n,r){"string"==typeof e&&(e=[[null,e,""]]);var i={};if(r)for(var o=0;o<this.length;o++){var a=this[o][0];null!=a&&(i[a]=!0)}for(var c=0;c<e.length;c++){var l=[].concat(e[c]);r&&i[l[0]]||(n&&(l[2]?l[2]="".concat(n," and ").concat(l[2]):l[2]=n),t.push(l))}},t}},function(e){e.exports=JSON.parse('{"ex1":"case leq 1 2 in inl x -> () | inr x -> fail","ex2":"fun x -> case leq x (add x 1) in inl y -> x | inr y -> fail","ex3":"fun x -> add x 1","ex4":"let rec f x = case leq 0 x in inl z -> add x (f (add x (-1))) | inr z -> 0 in case leq 0 (f ?) in inl y -> () | inr y -> fail"}')},function(e,t,n){"use strict";n.r(t);var r=n(1),i=n.n(r),o=n(0),a={insert:"head",singleton:!1};i()(o.a,a),o.a.locals;n.e(1).then(n.bind(null,8)).then(e=>{const t=n(3);let r=document.getElementById("examples");function i(e){if(e.Term){let t=document.createElement("li"),n=document.createElement("span");n.appendChild(document.createTextNode(e.Term.name+" : "+e.Term.type)),t.appendChild(n);let r=document.createElement("ul");return e.Term.children.forEach(e=>{r.appendChild(i(e))}),e.Term.children.length>0&&(r.classList.add("nested","active"),n.classList.add("caret","caret-down"),n.addEventListener("click",(function(){this.parentElement.querySelector(".nested").classList.toggle("active"),this.classList.toggle("caret-down")}))),t.appendChild(r),t}if(e.Binder){let t=document.createElement("li"),n=document.createElement("span");n.appendChild(document.createTextNode("["+e.Binder.name+" : "+e.Binder.type+"]")),t.appendChild(n);let r=document.createElement("ul");return r.appendChild(i(e.Binder.child)),t.appendChild(r),t}console.log("error")}Object.keys(t).forEach(e=>{let t=document.createElement("option");t.setAttribute("value",e),t.innerHTML=e,r.appendChild(t)}),r.addEventListener("change",e=>{document.getElementById("input").value=t[e.target.value]}),document.getElementById("cbv-button").addEventListener("click",(function(){let t=document.getElementById("input"),n=e.to_smtlib_cbv(t.value),r=document.getElementById("output");if(void 0===n.smtlib?r.value="":r.value=n.smtlib,void 0!==n.ast){let e=document.getElementById("ast");for(;e.firstChild;)e.removeChild(e.firstChild);let t=document.createElement("ul");t.setAttribute("style","margin: 0; padding: 0;"),t.appendChild(i(n.ast)),e.appendChild(t)}})),document.getElementById("cbn-button").addEventListener("click",(function(){let t=document.getElementById("input"),n=e.to_smtlib_cbn(t.value),r=document.getElementById("output");if(void 0===n.smtlib?r.value="":r.value=n.smtlib,void 0!==n.ast){let e=document.getElementById("ast");for(;e.firstChild;)e.removeChild(e.firstChild);let t=document.createElement("ul");t.setAttribute("style","margin: 0; padding: 0;"),t.appendChild(i(n.ast)),e.appendChild(t)}}))})}]);