const fs=require('fs'),path=require('path');
const {chromium}=require(process.env.CODEX_PRIMARY_RUNTIME_NODE_MODULES?process.env.CODEX_PRIMARY_RUNTIME_NODE_MODULES+'/playwright':'playwright');
const output=path.resolve(process.env.R_VIEWER_QA_OUT||'audit_runs/viewer_qa');
fs.mkdirSync(output,{recursive:true});
(async()=>{
 const browser=await chromium.launch({headless:true,args:['--no-sandbox','--disable-dev-shm-usage']});
 const page=await browser.newPage({viewport:{width:780,height:1000}});const errors=[];
 page.on('pageerror',e=>errors.push(e.message));
 await page.route(/^https?:/,r=>r.abort());
 await page.goto('file://'+process.cwd()+'/experiments/reciprocal/viewer.html');
 const frame=page.frameLocator('iframe');await frame.locator('#r-clock').waitFor();
 await page.waitForTimeout(250);
 const clock=await frame.locator('#r-clock').textContent();if(clock!=='459.9')throw Error('wrong initial time '+clock);
 await frame.locator('#r-phase').selectOption('4');if(await frame.locator('#r-clock').textContent()!=='720.0')throw Error('phase selection failed');
 for(const key of ['complet','impulsions','reglages','sans_transfert','sans_retour','sans_plasticite'])await frame.locator('#r-mode').selectOption(key);
 await frame.locator('#r-mode').selectOption('complet');
 await frame.locator('#r-time').evaluate(el=>{el.value=el.max;el.dispatchEvent(new Event('input',{bubbles:true}));});
 if(await frame.locator('#r-clock').textContent()!=='1000.0')throw Error('time slider failed');
 await frame.locator('#r-play').click();await page.waitForTimeout(250);await frame.locator('#r-play').click();
 if(await frame.locator('#r-clock').textContent()==='1000.0')throw Error('playback did not advance');
 await frame.locator('#r-phase').selectOption('4');
 await page.screenshot({path:path.join(output,'viewer_desktop.png'),fullPage:true});
 for(const width of [780,390,320]){
  await page.setViewportSize({width,height:1300});await page.waitForTimeout(150);
  const bad=await frame.locator('#r-reciproque').evaluate(root=>{
   const r=root.getBoundingClientRect();const els=[...root.querySelectorAll('svg text')];
   return els.filter(e=>{const b=e.getBoundingClientRect();return b.left<r.left-1||b.right>r.right+1;}).map(e=>({text:e.textContent,rect:e.getBoundingClientRect().toJSON()}));
  });
  if(bad.length)throw Error('labels outside at '+width+': '+JSON.stringify(bad));
 }
 await page.screenshot({path:path.join(output,'viewer_mobile.png'),fullPage:true});
 if(errors.length)throw Error(errors.join('\n'));
 console.log(JSON.stringify({offline:true,modes:6,time_slider:true,phase_select:true,play_pause:true,widths:[780,390,320],page_errors:errors}));
 await browser.close();
})().catch(e=>{console.error(e);process.exit(1)});
