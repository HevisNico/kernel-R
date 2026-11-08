// Execute the actual viewer script against its used DOM APIs; no browser claim.
const fs=require('fs'),vm=require('vm'),path=require('path');
const output=path.resolve(process.env.R_VIEWER_QA_OUT||'audit_runs/viewer_qa');
fs.mkdirSync(output,{recursive:true});
const input=fs.readFileSync(process.argv[2]||path.join(__dirname,'recorded_viewer_fragment.html'),'utf8');
const data=input.match(/<script id="r-recordings" type="application\/json">([\s\S]*?)<\/script>/)[1];
const script=[...input.matchAll(/<script>([\s\S]*?)<\/script>/g)].at(-1)[1];
const escape=s=>String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/"/g,'&quot;');
class Element{
 constructor(tag){this.tag=tag;this.attrs={};this.children=[];this.listeners={};this.value='';this.max='';this._text='';}
 setAttribute(k,v){this.attrs[k]=String(v);}appendChild(e){this.children.push(e);return e;}
 replaceChildren(...c){this.children=c;this._text='';}
 set textContent(s){this._text=String(s);this.children=[];}get textContent(){return this._text+this.children.map(x=>x.textContent).join('');}
 addEventListener(k,fn){this.listeners[k]=fn;}emit(k){if(this.listeners[k])this.listeners[k]({target:this});}
 xml(){return '<'+this.tag+' '+Object.entries(this.attrs).map(([k,v])=>k+'="'+escape(v)+'"').join(' ')+'>'+escape(this._text)+this.children.map(c=>c.xml()).join('')+'</'+this.tag+'>';}
}
(async()=>{
 const ids={};for(const id of ['r-reciproque','r-mode','r-phase','r-time','r-clock','r-step','r-graph','r-detail','r-play','r-recordings'])ids[id]=new Element(id==='r-graph'?'svg':'div');
 const root=ids['r-reciproque'];root.clientWidth=736;root.querySelector=s=>ids[s.slice(1)];ids['r-recordings'].textContent=data;ids['r-mode'].value='complet';
 let tick=null;
 const ctx={document:{getElementById:id=>ids[id],createElement:tag=>new Element(tag),createElementNS:(ns,tag)=>new Element(tag)},
 ResizeObserver:class{constructor(fn){this.fn=fn;}observe(){this.fn();}},setInterval:fn=>{tick=fn;return 1;},clearInterval:()=>{tick=null;},console};
 vm.runInNewContext(script,ctx);
 if(ids['r-clock'].textContent!=='459.9')throw Error('initial state');
 for(const mode of ['complet','impulsions','reglages','sans_transfert','sans_retour','sans_plasticite']){ids['r-mode'].value=mode;ids['r-mode'].emit('change');if(!ids['r-graph'].children.length)throw Error('mode not drawn');}
 ids['r-mode'].value='complet';ids['r-mode'].emit('change');ids['r-phase'].value='4';ids['r-phase'].emit('change');
 if(ids['r-clock'].textContent!=='720.0')throw Error('phase navigation');
 ids['r-time'].value=0;ids['r-time'].emit('input');if(ids['r-clock'].textContent!=='0.0')throw Error('time slider');
 ids['r-play'].emit('click');tick();tick();ids['r-play'].emit('click');if(tick!==null||ids['r-clock'].textContent==='0.0')throw Error('play/pause');
 ids['r-phase'].value='4';ids['r-phase'].emit('change');
 const sharp=require(process.env.CODEX_PRIMARY_RUNTIME_NODE_MODULES?process.env.CODEX_PRIMARY_RUNTIME_NODE_MODULES+'/sharp':'sharp');
 for(const width of [736,390,320]){
  root.clientWidth=width;ids['r-time'].emit('input');const graph=ids['r-graph'];graph.attrs.xmlns='http://www.w3.org/2000/svg';
  graph.children.unshift(new Element('style'));graph.children[0].textContent='text{font-family:DejaVu Sans,sans-serif;font-size:14px;fill:#1a1c1f}.r-name{font-weight:500}';
  const view=graph.attrs.viewBox.split(' ').map(Number);graph.attrs.width=width;graph.attrs.height=view[3];
  let svg=graph.xml().replaceAll('var(--foreground)','#1a1c1f').replaceAll('var(--border)','#cccccc').replaceAll('var(--viz-series-1)','#267d8d').replaceAll('var(--viz-series-2)','#9a5f38').replaceAll('var(--muted)','#e5e5e5').replace(/color-mix\([^)]*\)/g,'#e5eff1');
  const name=path.join(output,'diagram_'+width+'.svg');fs.writeFileSync(name,svg);await sharp(Buffer.from(svg)).flatten({background:'#ffffff'}).png().toFile(name.replace('.svg','.png'));
 }
 const report={method:'Node VM execution with minimal DOM and SVG rasterization; full browser not available',modes:6,time_slider:true,phase_navigation:true,play_pause:true,svg_widths:[736,390,320],passed:true};
 fs.writeFileSync(path.join(output,'interface_validation.json'),JSON.stringify(report,null,2));console.log(JSON.stringify(report));
})().catch(e=>{console.error(e);process.exit(1)});
