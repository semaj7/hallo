open util/boolean

abstract sig Profile{
	name:Name,
//	posted:set Content
}

sig Name{}
fact unique_names{all disjoint p,q:Profile | p.name != q.name}


-- PERSON -----------------------------------------------
---------------------------------------------------------

sig PersonalProfile extends Profile{
	eMail:one EMail,
	friends:set PersonalProfile,
	following:set Profile,
	blocked: set PersonalProfile,
	posted: set Content,
	isMember: set Member, //Jimmy: i'd prefer a other solution with groups:  isMemberOf: set GroupProfile
	canSee: set Content
}
fact symmetric_friends{all disjoint p,q:PersonalProfile | p in q.friends => q in p.friends}
fact no_reflexiv_friends{all p:Profile | not p in p.friends}
fact no_reflexiv_followers{all p:Profile | not p in p.following}
fact no_reflexiv_blocked{all p:Profile | not p in p.blocked}

fact unique_Emails{all disjoint p,q:PersonalProfile | p.eMail != q.eMail}
fact names_are_connected{Name in Profile.name}  

sig EMail{}
fact eMail_are_connected{EMail in PersonalProfile.eMail}


-- GROUP ----------------------------------------------
-------------------------------------------------------

sig GroupProfile extends Profile {
	posted: set CommentableContent
	// Jimmy: maybe: members: set PersonalProfile
	
}
 
--== is this true?

//fact atLeast_one_admin_per_group{all g:GroupProfile,  m:Member | m.memberOf=g && isTrue[m.isAdmin]}
//Pascal: I think this won't work, it only says that ther is some group with a admin, and not that every group has an admin
//Jimmy: "Some of the group members are designated as the group’s administrators."  therefore every group has at least one admin.

//can a member be member and follow a group?
//Pascal: i think he cant. "Users who are not members of a group can still follow the group"
//Jimmy: but there is no connection declared between being member of the group and the newsfeed. to me, this sounds as if a members can decide to let the content be displayed in the newsfeed by following their group.
fact cant_be_member_and_follow{all p:PersonalProfile, m:Member, g:GroupProfile | (m in p.isMember && g=m.memberOf) => (not g in p.following)}

sig Member {
	isAdmin:Bool,
	memberOf: one GroupProfile
}
fact unique_members{all disjoint p,q:PersonalProfile, m:Member | m in p.isMember => not m in q.isMember}
fact members_are_connected{Member in PersonalProfile.isMember}

fact only_once_member_of_a_group{
	all p:PersonalProfile, disjoint m,n:Member, g:GroupProfile | (g=m.memberOf && m in p.isMember) => not (g=n.memberOf && n in p.isMember)
}



//Pascal: solution of the other group (Andres, Panuya, Fabian): a signature admin_group, with a set of persons.
//Jimmy : I think the solution we have is quite elegant, since people can easily find the groups they are member of, and if they are the admin of it or not.



-- CONTENT ----------------------------------------------
---------------------------------------------------------

abstract sig Content{
	visible: Visible,
	createdby: PersonalProfile
}
fact groupcontent_is_public/privat{all g:GroupProfile,c:CommentableContent |
						c in g.posted => (c.visible = Public || c.visible = Private)}

fact {all p:PersonalProfile | {all c:p.posted | c.createdby = p}}
//fact {all g:GroupProfile, p:PersonalProfile | g.posted.createdby = p
//fact member_of_group_you_post_in

//Pascal: solution of the other group (Andres, Panuya, Fabian): they have a field created_by, and owned_by in every content, but our solution should be fine too.
//Pascal: do we need to keep track of the initial creator of a content? 
//Jimmy: It's not declared, but if we someday want to implement a 'delete content' function, we'd need to keep track of the creator. So, i would.

fact unique_personalPosts{all disjoint p,q:PersonalProfile, c:Content | c in p.posted => not c in q.posted}
fact unique_groupPosts{all disjoint p,q:GroupProfile, c:Content | c in p.posted => not c in q.posted}
fact unique_posts{all p:PersonalProfile, q:GroupProfile, c:Content | c in p.posted => not c in q.posted}  

fact post_are_connected{Content in PersonalProfile.posted}

abstract sig CommentableContent extends Content{}
abstract sig PersonalContent extends Content{}

sig Photo extends CommentableContent{}
sig Post extends CommentableContent{
	//Jimmy: should Text be declared 'lone' ?
	post: Text, 
	link: set Photo
}
sig Comment extends CommentableContent{
	//Jimmy : 'lone'?
	comment: Text, 
	refersTo: one CommentableContent
}
//Pascal: what's the visibility of comments? (i will ask the TA) -- if post is friends cann comment be public?
//Pascal: i think we need an additional fact to make sure that the one who posts a comment actually sees the content to which the comment refers.
fact sees_commentableContent{all p:PersonalProfile, c:Comment | c in p.posted && c.refersTo in p.canSee}
fact same_visibleType{all c:Comment | c.visible = c.refersTo.visible}
fact no_refl_refersTo{all c:Comment | c != c.refersTo}

fact no_cyclic_comments{all c:Comment | not c in (c.*refersTo)}

sig PersonalMessage extends PersonalContent{
	message: Text,
	includedPhoto: set Photo,
	sendTo: PersonalProfile
}
sig PersonalDetails extends PersonalContent{
	details:Text
}
sig Text{}

-- OTHER STUFF -------------------------------------------
---------------------------------------------------------


abstract sig Visible {}
one sig Private, Friends, FriendsOfFriends, TransitiveFriends, Public extends Visible{}




-- OTHER STUFF -------------------------------------------
---------------------------------------------------------

fact canSee{all disjoint p:PersonalProfile,c:Content | 
		(c in p.posted ||
		(c.visible = Friends && c in p.friends.posted) ||
		(c.visible = FriendsOfFriends && (c in p.friends.posted || c in p.friends.friends.posted)) ||
		(c.visible = TransitiveFriends && c in p.^friends.posted) ||
		(c.visible = Public))
		=> c in p.canSee }
//Pascal: We should actually do this as a predicate (Task C)

//Pascal: the receiver of a message can always see it.
//Pascal: we need to make sure that a user can't see contents from users that blocked him
//Pascal: a user can see the private content of his groups


-- TASK C ------------------------------------------------
---------------------------------------------------------

pred canSee [p:PersonalProfile, c: Content] { 
	
}

pred canModify[p:PersonalProfile, c: Content] {

}

pred isOnNewsFeed [p:PersonalProfile, c: Content] {

}

-- TASK D ------------------------------------------------
---------------------------------------------------------

//Invariante 1
//Comment chains are acyclic
/*assert inv1{
	all c:comment | c not in c.^attached_to
}*/


//Invariante 2
//A user can modify only content they can see
assert inv2 {
	
}


//Invariante 3
//A user can modify all the content they have created
assert inv3 {

}


//Invariante 4
//If a post or message includes photos, the photos are visible at least to all the people that can view the post
assert inv4 {

} 

//invariante 5
//Each group has members
assert inv5 {
}


//Invariante 6
//A user’s newsfeed only has content visible to her
assert inv6 {

} 


//Invariante 7
//A user cannot see any content created by a user that blocks them
assert inv7 {

}


-- SHOW -------------------------------------------------
---------------------------------------------------------

pred show() {
//	all p:PersonalProfile | #p.following >= 1
//	all p:PersonalProfile | #p.friends >= 1
//	some p:PersonalProfile | #p.posted >= 2
//	some p:PersonalProfile | #p.isMember >= 2
//	#Post >=1
	#Comment >=4
//	# PersonalMessage >=4

//	#Photo >=5
//	#PersonalProfile >= 2
//	#GroupProfile

}
pred show2(){}
run show for 5// but 4 Comment
	
